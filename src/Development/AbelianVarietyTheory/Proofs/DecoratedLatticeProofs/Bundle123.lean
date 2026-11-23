module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle139
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle092
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle089
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RightTranslationActionApply
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle143
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle147
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle010
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle115
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle116
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightWith
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem host_tie_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)), GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.HostTie (numDatumOfParameters (I.rec7 l Z) L) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (B.primes X) := by
  intro B X I h l Z L
  have hX : B.fields.Ok := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1.1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ := host_fields_primes_ties I h hX l Z
  refine ⟨rfl, rfl, rfl, h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_, fun _ => rfl, HEq.rfl⟩
  · rw [h9]
    rfl
  · intro i; rw [h10]; rfl
end GlobalTheory.CoreHt
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GramAnnih

variable {D : D7} {m n : ℕ}

theorem pairing_rat (T : Matrix (Fin m) (Fin m) D.host.E) (ψ : AddChar (AF D.host.F) ℂ)
    (ξ : Matrix (Fin m) (Fin n) D.host.E) (x : Mx D m n) :
    GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) x =
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (GlobalTheory.MixModel.rat (ξᴴ * T) * x))) := by
  rw [rat_mul, rat_conjTranspose]
  rfl

theorem rat_single (j : Fin n) (i : Fin m) (e : D.host.E) :
    GlobalTheory.MixModel.rat (D := D) (Matrix.single j i e) = Matrix.single j i (incA D e) :=
  Matrix.map_single j i e (incA D)

theorem trace_tmul_half (t : AF D.host.F) :
    Algebra.trace (AF D.host.F) (AE D) (t ⊗ₜ[D.host.F] (2 : D.host.E)⁻¹) = t := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have e : (2 : D.host.E)⁻¹ = algebraMap D.host.F D.host.E 2⁻¹ := by rw [map_inv₀, map_ofNat]
  rw [e, GlobalTheory.LatVac.trace_tmul, Algebra.trace_algebraMap, D.sp.cm.deg2]
  simp

theorem ratMx_annihilator : ∀ (D : D7) (m n : ℕ) (T : Matrix (Fin m) (Fin m) D.host.E), IsHermND D.sp.cm.sig T → ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → (∀ x : Mx D m n, (∀ γ ∈ ratMx D m n, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ γ x = 1) ↔ x ∈ ratMx D m n) ∧ ∀ γ ∈ ratMx D m n, (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ γ x = 1) → γ = 0 := by
  intro D m n T hT ψ hψ
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have hU : IsUnit T.det := isUnit_iff_ne_zero.2 hT.2
  refine ⟨fun x => ⟨fun h => ?_, ?_⟩, ?_⟩
  · have key : ∀ i j (e : D.host.E), ψ (Algebra.trace (AF D.host.F) (AE D) (incA D e * x i j)) = 1 := by
      intro i j e
      have h1 := h _ (rat_mem (Matrix.single j i e * T⁻¹)ᴴ)
      rw [pairing_rat, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_mul_cancel_right _ _ hU, rat_single,
        Matrix.trace_single_mul, smul_eq_mul] at h1
      exact h1
    have hent : ∀ i j, ∃ e : D.host.E, x i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := fun i j =>
      GlobalTheory.RatAnnih.tensor_rat (x i j) fun e =>
        (GlobalTheory.SWQ.Annihilator.self_annihilator D.host.F inferInstance ψ hψ).2 _ fun c =>
          (congrArg ψ (GlobalTheory.RatAnnih.trace_mul_algebraMap (x i j) e c)).trans (key i j (c • e))
    choose M hM using hent
    exact ⟨Matrix.of M, Matrix.ext fun i j => (hM i j).symm⟩
  · rintro ⟨η, rfl⟩ _ ⟨ξ, rfl⟩
    change GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) (GlobalTheory.MixModel.rat η) = 1
    have e : Matrix.trace (GlobalTheory.MixModel.rat (D := D) (ξᴴ * T * η)) =
        (1 : AF D.host.F) ⊗ₜ[D.host.F] Matrix.trace (ξᴴ * T * η) :=
      (AddMonoidHom.map_trace (incA D) _).symm
    rw [pairing_rat, ← rat_mul, e, GlobalTheory.LatVac.trace_tmul, one_mul]
    exact hψ.2.2.1 _
  · rintro _ ⟨ξ, rfl⟩ h
    change GlobalTheory.MixModel.rat ξ = 0
    have hM : ξᴴ * T = 0 := by
      refine Matrix.ext fun j i => ?_
      by_contra ha
      replace ha : (ξᴴ * T) j i ≠ 0 := ha
      obtain ⟨t, ht⟩ := hψ.2.2.2
      have h1 : GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) _ = 1 :=
        h (Matrix.single i j (t ⊗ₜ[D.host.F] ((2 : D.host.E)⁻¹ * ((ξᴴ * T) j i)⁻¹)))
      have e : (t ⊗ₜ[D.host.F] ((2 : D.host.E)⁻¹ * ((ξᴴ * T) j i)⁻¹)) * GlobalTheory.MixModel.rat (D := D) (ξᴴ * T) j i =
          t ⊗ₜ[D.host.F] (2 : D.host.E)⁻¹ := by
        change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (ξᴴ * T) j i) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel_right₀ ha]
      rw [pairing_rat, Matrix.trace_mul_comm, Matrix.trace_single_mul, smul_eq_mul, e, trace_tmul_half] at h1
      exact ht h1
    have h0 : ξᴴ = 0 := by
      rw [← Matrix.mul_nonsing_inv_cancel_right T ξᴴ hU, hM, Matrix.zero_mul]
    rw [Matrix.conjTranspose_eq_zero.1 h0, rat_zero]

end GlobalTheory.GramAnnih
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

open scoped ContDiff

namespace GlobalTheory.CjNeg

variable {D : D7}

theorem inv_neg_mat {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      exact h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  have hn : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h1 : ψ a * ψ (-a) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h2 : starRingEnd ℂ (ψ a) * ψ a = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  calc starRingEnd ℂ (ψ a) = starRingEnd ℂ (ψ a) * (ψ a * ψ (-a)) := by rw [h1, mul_one]
    _ = ψ (-a) := by rw [← mul_assoc, h2, one_mul]

theorem symplOH_negT (S T : HSp D) (x y : WO S T) :
    symplOH S (GlobalTheory.ChiGrid.negSp T) x y = -symplOH S T x y := by
  simp only [symplOH, symplO, hO, GlobalTheory.ChiGrid.negSp_gram, Matrix.neg_apply, map_neg, neg_mul, mul_neg,
    Finset.sum_neg_distrib]

theorem symplOH_negS (S T : HSp D) (x y : WO S T) :
    symplOH (GlobalTheory.ChiGrid.negSp S) T x y = -symplOH S T x y := by
  simp only [symplOH, symplO, hO, GlobalTheory.ChiGrid.negSp_gram, inv_neg_mat, Matrix.neg_apply, map_neg, neg_mul, mul_neg,
    Finset.sum_neg_distrib]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem heis_negT {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ S (GlobalTheory.ChiGrid.negSp T) w (cj id f) = cj id (heisO ψ S T w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negT]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem heis_negS {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ (GlobalTheory.ChiGrid.negSp S) T w (cj id f) = cj id (heisO ψ S T w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negS]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem heis_negT' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ S T w (cj id f) = cj id (heisO ψ S (GlobalTheory.ChiGrid.negSp T) w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negT, neg_neg]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem heis_negS' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ S T w (cj id f) = cj id (heisO ψ (GlobalTheory.ChiGrid.negSp S) T w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negS, neg_neg]

theorem contDiff_conj {k : ℕ} {g : (Fin k → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun t => starRingEnd ℂ (g t) :=
  Complex.conjCLE.contDiff.comp hg

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem theta_negT {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S (GlobalTheory.ChiGrid.negSp T) (cj id f) := {
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH S (GlobalTheory.ChiGrid.negSp T) (ratW T S γ) w)) * starRingEnd ℂ (f w)
    rw [hf.quasi, map_mul, conj_psi hψ, symplOH_negT]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negT hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w) }

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem theta_negT' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S (GlobalTheory.ChiGrid.negSp T) f) : IsThetaFunO ψ S T (cj id f) := {
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH S T (ratW T S γ) w)) * starRingEnd ℂ (f w)
    have hq : f (ratW T S γ + w) = ψ (-(symplOH S (GlobalTheory.ChiGrid.negSp T) (ratW T S γ) w)) * f w := hf.quasi γ w
    rw [hq, map_mul, conj_psi hψ, symplOH_negT, neg_neg]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negT' hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w) }

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem theta_negS {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T (cj id f) := {
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH (GlobalTheory.ChiGrid.negSp S) T (ratW T S γ) w)) * starRingEnd ℂ (f w)
    rw [hf.quasi, map_mul, conj_psi hψ, symplOH_negS]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negS hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w) }

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem theta_negS' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f) : IsThetaFunO ψ S T (cj id f) := {
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH S T (ratW T S γ) w)) * starRingEnd ℂ (f w)
    have hq : f (ratW T S γ + w) = ψ (-(symplOH (GlobalTheory.ChiGrid.negSp S) T (ratW T S γ) w)) * f w := hf.quasi γ w
    rw [hq, map_mul, conj_psi hψ, symplOH_negS, neg_neg]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negS' hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w) }

theorem cj_id_cj_id {S T : HSp D} (f : WO S T → ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = f :=
  GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj_cj id id (fun _ => rfl) f

theorem theta_heis_neg : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, (∀ f : WO S T → ℂ, (IsThetaFunO ψ S (GlobalTheory.ChiGrid.negSp T) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) ↔ IsThetaFunO ψ S T f) ∧ (IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) ↔ IsThetaFunO ψ S T f)) ∧ ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ S (GlobalTheory.ChiGrid.negSp T) w (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (heisO ψ S T w f) ∧ heisO ψ (GlobalTheory.ChiGrid.negSp S) T w (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (heisO ψ S T w f) := by
  intro D ψ hψ S T
  refine ⟨fun f => ⟨⟨fun h => ?_, theta_negT hψ⟩, ⟨fun h => ?_, theta_negS hψ⟩⟩, fun w f => ⟨heis_negT hψ S T w f, heis_negS hψ S T w f⟩⟩
  · simpa only [cj_id_cj_id] using theta_negT' hψ h
  · simpa only [cj_id_cj_id] using theta_negS' hψ h

end GlobalTheory.CjNeg
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.mixed_model_central_terms_gram_identities : ∀ D : D7, (∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), (∀ x : Mx D T.rank ρ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T (d.extX T x) ⬝ x = d.jY ⬝ (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D)) ∧ ∀ (c : skewA D ρ) (x : Mx D T.rank ρ), d.qS T c x = -(algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D) ⬝ c.1).trace)) ∧ ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (c : skewA D ρ) (y : Mx D S.rank ρ), d.qT S c y = -(algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) ((incA D D.host.xi0⁻¹ • (adj y ⬝ (gA S ⬝ y))) ⬝ c.1).trace) := by
  first | exact @GlobalTheory.CentralGram.central_gram | exact GlobalTheory.CentralGram.central_gram | (intros; apply GlobalTheory.CentralGram.central_gram <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.TransvAdelic

theorem transv_unitary : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvUnitary D :=
  fun D => (transv_unitary_conj D).1

end GlobalTheory.TransvAdelic
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.unitaryTransvection_unitary_and_conjugation : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvUnitary D ∧ GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvConj D := by
  first | exact @GlobalTheory.TransvAdelic.transv_unitary_conj | exact GlobalTheory.TransvAdelic.transv_unitary_conj | (intros; apply GlobalTheory.TransvAdelic.transv_unitary_conj <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Core.Rk
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.RowRead

theorem map_mem_span_range {K L M N J : Type*} [Semiring K] [Semiring L] [AddCommMonoid M] [AddCommMonoid N] [Module K M]
    [Module L N] {σ : K →+* L} (f : M →ₛₗ[σ] N) {φ : J → M} (h : Submodule.span K (Set.range φ) = ⊤) (z : M) :
    f z ∈ Submodule.span L (Set.range fun a => f (φ a)) := by
  have hz : z ∈ Submodule.span K (Set.range φ) := h ▸ Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact Submodule.subset_span ⟨a, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

section G
open GlobalTheory.PeriodOnStep
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) {I : ChainIn X.E X.K X.Tau R} (b0 : (I.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (I.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (I.S R.m).G b0)
  (tz : X.E) (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ)

def valMt (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b)) :
    (perOn W Ch sel mu P b0 til ext tz H).Mt X.emb σ →ₗ[ℂ] ((stepX Ch sel mu P).D () → Pol ℂ X.Tau (R.N R.m - 1)) where
  toFun F p := F.1 () p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def valMtP : MtP W Ch sel mu P σ →ₗ[ℂ] ((stepX Ch sel mu P).D () → Pol ℂ X.Tau (R.N R.m - 1)) where
  toFun G p := G.1 (toRow sel mu p.1.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem valMtP_injective : Function.Injective (valMtP W Ch sel mu P σ) := by
  intro G G' h
  refine Subtype.ext (funext fun d => ?_)
  obtain ⟨p, rfl⟩ := toRow_surjective sel mu d
  exact congrFun h (trivPt X _ _ _ _ p)

theorem rowEmb_linearIndependent (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b)) {J : Type} {φ : J → MtildeV W Ch sel mu P}
    (h : LinearIndependent X.K φ) :
    LinearIndependent ℂ fun a => rowEmb W Ch sel mu P b0 til ext tz H hd σ (φ a) :=
  LinearIndependent.of_comp (valMt W Ch sel mu P b0 til ext tz σ H)
    ((toMtilde_linearIndependent W Ch sel mu P σ h).map' (valMtP W Ch sel mu P σ)
      (LinearMap.ker_eq_bot.2 (valMtP_injective W Ch sel mu P σ)))

theorem rowEmb_span (hX : X.Ok) {J : Type} {φ : J → MtildeV W Ch sel mu P} (h : Submodule.span X.K (Set.range φ) = ⊤) :
    Submodule.span ℂ (Set.range fun a => rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ (φ a)) = ⊤ :=
  GlobalTheory.PerQ.RowIntModel.eq_top_of_rowEmb_mem W Ch sel mu P b0 til ext tz hd σ hX _ fun z _ =>
    map_mem_span_range (rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ) h z

end G

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

end GlobalTheory.Core.Rk.RowRead

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.linearIndependent_of_ne_zero_of_isParamFunV_of_separated : ∀ (D : D7) (V : HSp D) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (ι : Type) (f : ι → (GA D V → ℂ)) (B : ι → GlobalTheory.LFun.Fam D.host.E), (∀ i, f i ≠ 0) → (∀ i, GlobalTheory.LFun.IsParamFunV V Sb (f i) (B i)) → (∀ i i', i ≠ i' → ∃ w ∉ GlobalTheory.LFun.above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F))), B i w ≠ B i' w) → LinearIndependent ℂ f := by
  first | exact @GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV | exact GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV | (intros; apply GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV <;> assumption)
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem collS_on : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ S : Set ℝ, AmpOn S → CountBoundOn S → SmallOn S → TieOn S → On S CollS := by
  intro hSMR S hAmp hCnt hSmall hTie
  intro Cg cb Cu cT CT hcb hcT
  obtain ⟨c3, cH, thr1, hC⟩ := hCnt Cg cb Cu cT CT
  obtain ⟨cV, thr2, hT⟩ := hTie Cg cb Cu cT CT
  obtain ⟨Ca, C2, Ch, -, hCh, hA⟩ := hAmp Cg cb Cu cT CT hcb hcT
  set c : ℝ := max (max (max (max c3 1) CT) (|cH| + 2)) (|cV| + 2) with hc
  have hc3 : c3 ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) (le_max_left _ _))
  have hc1 : 1 ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) (le_max_left _ _))
  have hcT' : CT ≤ c := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hcH : |cH| + 2 ≤ c := le_trans (le_max_right _ _) (le_max_left _ _)
  have hcV : |cV| + 2 ≤ c := le_max_right _ _
  set C : ℝ := max (max (max (max (max c (4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2))) (2 * C2)) |Ca|)
    (408 * (Real.exp 1 * Real.pi))) CT with hCdef
  have hCc : c ≤ C := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hC4 : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hC2 : 2 * C2 ≤ C := le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hCa : |Ca| ≤ C := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hC408 : 408 * (Real.exp 1 * Real.pi) ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCT : CT ≤ C := le_max_right _ _
  obtain ⟨thr3, hA3⟩ := hA (9 * c + 3) 1 one_pos
  obtain ⟨thr4, hS⟩ := hSmall Cg cb Cu cT CT 1 hcb hcT one_pos
  obtain ⟨thr5, hsum⟩ := GlobalTheory.T.collisionAbsSum_bound_of_two_rowBounds hSMR CT C hC408 hCT
  refine ⟨max (max (max (max (max thr1 thr2) thr3) thr4) thr5) (max (3 * |C2|) 4), ?_⟩
  intro C0 hC0 C' Cl hC' hCl D large₂ X Y hF hI u hCG hTies hadm hH0 hConc hAbs
  have hle : ∀ {x : ℝ}, max (max (max (max (max thr1 thr2) thr3) thr4) thr5) (max (3 * |C2|) 4) ≤ x →
      thr1 ≤ x ∧ thr2 ≤ x ∧ thr3 ≤ x ∧ thr4 ≤ x ∧ thr5 ≤ x ∧ 3 * |C2| ≤ x ∧ 4 ≤ x := by
    intro x hx
    simp only [max_le_iff] at hx
    exact ⟨hx.1.1.1.1.1, hx.1.1.1.1.2, hx.1.1.1.2, hx.1.1.2, hx.1.2, hx.2.1, hx.2.2⟩
  obtain ⟨h1', h2', h3', h4', h5', h6', h7'⟩ := hle hC'
  obtain ⟨h1l, h2l, h3l, h4l, h5l, -, h7l⟩ := hle hCl
  have hCnt' := hC C0 hC0 C' Cl h1' h1l D large₂ u
  have hc3' := hCnt'.1 c hc3
  obtain ⟨T, Z, hTA, hVol⟩ := hT C0 hC0 C' Cl h2' h2l D large₂ X Y hF hI u hTies hH0 hConc
  have hAmpAt := hA3 C0 hC0 C' Cl h3' h3l D large₂ hCG hTies hadm hConc.2.2.2.2.2.2.2
  have hSm := hS C0 hC0 C' Cl h4' h4l D large₂ hTies hadm
  have hHyp : Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 :=
    Formalism.MainNotions.count_hypotheses_diagonal_words D large₂ C' Cl Cg cb Cu cT CT C0 1 hH0.2.1 hH0.1 hH0.2.2 (by linarith) (by linarith) le_rfl u
  have hC2' : |C2| ≤ C' := by have := abs_nonneg C2; linarith
  have hDeg := GlobalTheory.T.degenerateCollision_rowBound_at_sizeData CT cH cV Ca C2 Ch c C hc1 hcT' hcH hcV hCh hCc hC4 hC2 hCa D large₂ u T Z C' Cl Cg cb Cu cT C0
    h6' hHyp hc3' hCnt'.2 hVol hAmpAt hSm hTA.2.2.2.1 hTA.2.2.2.2.1 hTA.2.2.2.2.2.1
  have hND := GlobalTheory.T.nondegenerateCollision_rowBound_at_parameters CT cH cV Ca C2 Ch c C hc1 hcH hcV hCh hCc hC4 D large₂ u T Z C' Cl Cg cb Cu cT C0
    hC2' hHyp hc3' hCnt'.2 hVol hAmpAt hSm hTA.2.2.2.1 hTA.2.2.2.2.1 hTA.2.2.2.2.2.1
  exact hsum D large₂ X Y hF hI u T Z C' Cl Cg cb Cu cT C0 h5' h5l hH0 hConc hAbs hTA (hSm.2.2.2.2 hH0 u) hND hDeg

end GlobalTheory.Core.Deg
end
