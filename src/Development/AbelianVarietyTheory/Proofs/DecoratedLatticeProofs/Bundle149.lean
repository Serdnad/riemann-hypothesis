module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionHermitianFrames
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle106
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Formalism.LocalRingCardinality.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

variable {D : D7}

theorem linInd_e {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : LinearIndependent D.host.E d.e.transpose := by
  show LinearIndependent D.host.E (fun i : Fin ρ => fun k : Fin W.rank => d.e k i)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : d.e *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← this]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : (d.e'ᴴ * W.gram * d.e) *ᵥ g = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  rw [d.e'e, Matrix.one_mulVec] at h2
  intro i; exact congrFun h2 i

theorem gramQ_e {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : gramQ W d.e = 0 := by
  rw [gramQ, ← Matrix.mul_assoc]; exact d.ee

theorem flagUnipotent_anisotropic_projection_eq_one {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) {n : GA D W} (hn : n ∈ flagN d) :
    d.p0 ⬝ (mt W n ⬝ d.j0) = 1 := by
  obtain ⟨u, -, b, c, rfl⟩ := ((flag_jacobi_structure D W W₀ ρ d).1 n).1 hn
  rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.wittDecomp_levi_inclAnisotropic,
    ← Matrix.mul_assoc (mt W (d.levi u)) d.jX, d.levi_jX, Matrix.mul_add, d.p0_j0, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, Matrix.zero_mul, add_zero]

theorem Rgrp_eq {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : Rgrp W (rat d.e) = jacGrp d := by
  have dec := flag_jacobi_structure D W W₀ ρ d
  ext r
  constructor
  · rintro ⟨u, hu, hr⟩
    have hs : d.levi u⁻¹ * r ∈ stabX d := by
      show mt W (d.levi u⁻¹ * r) ⬝ d.jX = d.jX
      rw [mt_mul, Matrix.mul_assoc, show mt W r ⬝ d.jX = d.jX ⬝ u.1 from hr, ← Matrix.mul_assoc, d.levi_jX,
        Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    obtain ⟨n, hn, h, he⟩ := (dec.2.2.1 _).1 hs
    have hl : d.levi u ∈ flagN d := (dec.1 _).2 ⟨u, hu, 0, 0, by rw [d.nB_zero, d.nC_zero, mul_one, mul_one]⟩
    refine (dec.2.2.2.1 r).2 ⟨d.levi u * n, mul_mem hl (Subgroup.mem_inf.1 hn).1, h, ?_⟩
    rw [mul_assoc, ← he, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  · intro hr
    obtain ⟨n, hn, h, rfl⟩ := (dec.2.2.2.1 r).1 hr
    obtain ⟨u, hu, b, c, rfl⟩ := (dec.1 n).1 hn
    refine ⟨u, hu, ?_⟩
    show mt W _ ⬝ d.jX = d.jX ⬝ u.1
    rw [mt_mul, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.nC_jX, d.nB_jX,
      d.levi_jX]

theorem flagUnipotent_mul_emb_mem_rational_iff {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) {n : GA D W} (hn : n ∈ flagN d) (h : GA D W₀) :
    n * d.emb0 h ∈ GQ W ↔ n ∈ GQ W ∧ h ∈ GQ W₀ := by
  constructor
  · intro hg
    have hh : h ∈ GQ W₀ := by
      rw [mem_GQ_iff] at hg ⊢
      have e : mt W₀ h = d.p0 ⬝ (mt W (n * d.emb0 h) ⬝ d.j0) := by
        rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt W n), ← Matrix.mul_assoc, flagUnipotent_anisotropic_projection_eq_one d hn,
          Matrix.one_mul]
      rw [e]
      exact ratMx_mul (rat_mem _) (ratMx_mul hg (rat_mem _))
    refine ⟨?_, hh⟩
    have : n = n * d.emb0 h * (d.emb0 h)⁻¹ := by rw [mul_inv_cancel_right]
    rw [this]
    exact mul_mem hg (inv_mem (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hh))
  · rintro ⟨h1, h2⟩
    exact mul_mem h1 (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h2)

theorem base_point : ∀ (D : D7) (W W₀ : HSp D) (ρ : ℕ) (d : HypDec W W₀ ρ), IsBase W d.e ∧ gramQ W d.e = 0 ∧ xZero d = rat d.e ∧ Rgrp W (rat d.e) = jacGrp d ∧ Continuous d.emb0 ∧ ∀ n ∈ flagN d, ∀ h, n * d.emb0 h ∈ GQ W ↔ n ∈ GQ W ∧ h ∈ GQ W₀ := by
  intro D W W₀ ρ d
  refine ⟨⟨linInd_e d, fun u _ => ?_⟩, gramQ_e d, rfl, Rgrp_eq d, d.continuous_embed, fun n hn h => flagUnipotent_mul_emb_mem_rational_iff d hn h⟩
  rw [gramQ_e d, rat_zero, Matrix.zero_mul, Matrix.mul_zero]

end GlobalTheory.Unf
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.WittOrbit
variable {D : D7}

theorem isQA_sig (D : D7) : GlobalTheory.SgAlg.IsQA (D.sp.cm.sig : D.host.E →+* D.host.E) := by
  refine ⟨fun x => star_star x, ?_, inferInstance, ?_, fun x _ hx => isUnit_iff_ne_zero.2 hx⟩
  · by_contra h
    push_neg at h
    have hbot : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ :=
      eq_top_iff.2 fun x _ => Algebra.mem_bot.2 ((D.sp.cm.fixed x).1 (h x))
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 hbot
    rw [D.sp.cm.deg2] at h1
    exact absurd h1 (by norm_num)
  · exact isUnit_iff_ne_zero.2 two_ne_zero

theorem free_of_li {n ρ : ℕ} (x : Matrix (Fin n) (Fin ρ) D.host.E) (h : LinearIndependent D.host.E x.transpose) :
    GlobalTheory.SgAlg.Free x := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' x)
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem isUnit_of_unitary (W : HSp D) {g : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (h : gᴴ * W.gram * g = W.gram) : IsUnit g := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact gram_det_ne W this.symm

theorem orb_eq_orbit : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E),
    LinearIndependent D.host.E x₀.transpose →
      (∀ x ∈ Orb W x₀, ∃ γ ∈ GQ W, mt W γ ⬝ (rat x₀ : Mx D W.rank ρ) = rat x) ∧
        ∀ γ ∈ GQ W, ∀ x ∈ Orb W x₀, ∃ x' ∈ Orb W x₀, mt W γ ⬝ (rat x : Mx D W.rank ρ) = rat x' := by
  intro D W ρ x₀ h₀
  have hJ : GlobalTheory.SgAlg.IsHermU (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram :=
    ⟨gram_conjTranspose W, gram_isUnit_det W⟩
  refine ⟨fun x hx => ?_, fun γ hγ x hx => ?_⟩
  · obtain ⟨g, hg, hgx⟩ := GlobalTheory.SgAlg.witt_free_field _ (isQA_sig D) W.gram hJ x₀ x (free_of_li x₀ h₀)
      (free_of_li x hx.1) (by
        show x₀ᴴ * W.gram * x₀ = xᴴ * W.gram * x
        rw [Matrix.mul_assoc, Matrix.mul_assoc]
        exact hx.2.symm)
    have hg' : gᴴ * W.gram * g = W.gram := hg
    have hu : adj (rat g) * (gA W * rat g) = gA W := by
      rw [← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, ← Matrix.mul_assoc, hg']
    refine ⟨ofMat W (rat g) hu, (mem_GQ_iff W _).2 ⟨g, rfl⟩, ?_⟩
    rw [mt_ofMat, ← rat_mul, hgx]
  · obtain ⟨g, hg⟩ := (mem_GQ_iff W γ).1 hγ
    replace hg : rat g = mt W γ := hg
    have hu : gᴴ * W.gram * g = W.gram := rat_injective (by
      rw [rat_mul, rat_mul, rat_conjTranspose, hg]
      exact mt_rel W γ)
    have hgu := isUnit_of_unitary W hu
    refine ⟨g * x, ⟨?_, ?_⟩, by rw [← hg, ← rat_mul]⟩
    · refine Matrix.mulVec_injective_iff.1 ?_
      intro v w hvw
      simp only [← Matrix.mulVec_mulVec] at hvw
      exact Matrix.mulVec_injective_iff.2 hx.1 (Matrix.mulVec_injective_iff_isUnit.2 hgu hvw)
    · show (g * x)ᴴ * (W.gram * (g * x)) = gramQ W x₀
      rw [← hx.2, gramQ, Matrix.conjTranspose_mul]
      calc xᴴ * gᴴ * (W.gram * (g * x)) = xᴴ * ((gᴴ * W.gram * g) * x) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hu]

end GlobalTheory.WittOrbit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem exists_GQ_of_unitary {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (γ : GL (Fin n) D.host.E)
    (hγ : γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)
      (Matrix.reindex (finCongr hn) (finCongr hn) (HSpace.gram V))) :
    ∃ a : GA D V, a ∈ GQ V ∧
      GlobalTheory.AdForm.finM V hn a =
        (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ).1 ∧
      ∀ τ, GlobalTheory.AdForm.infM θ V hn a τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ _) τ := by
  subst hn
  have hγ' : Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) γ.1 * HSpace.gram V * γ.1 = HSpace.gram V := hγ
  have hmem : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ ∈
      HR (AF D.host.F) (Formalism.L2.Forms.sigD D) (HSpace.gram V) := by
    change Formalism.UG.cT (sigR (AF D.host.F) (Formalism.L2.Forms.sigD D)) (γ.1.map (inclR (F := D.host.F) (AF D.host.F))) *
      (HSpace.gram V).map (inclR (F := D.host.F) (AF D.host.F)) * γ.1.map (inclR (F := D.host.F) (AF D.host.F)) =
      (HSpace.gram V).map (inclR (F := D.host.F) (AF D.host.F))
    have e : Formalism.UG.cT (sigR (AF D.host.F) (Formalism.L2.Forms.sigD D)) (γ.1.map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) γ.1).map (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j
      rfl
    rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hγ']
  refine ⟨⟨_, hmem⟩, ⟨γ, hγ', rfl⟩, ?_, fun τ => ?_⟩
  · ext i j
    rfl
  · ext i j
    exact (hθ τ).1 (γ.1 i j)

theorem exists_GQ_of_unitary0 : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ γ : GL (Fin (D.R.N 0)) D.host.E, γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → ∃ a : GA D (D.sp.X 0), a ∈ GQ (D.sp.X 0) ∧ GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ).1 ∧ ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ _) τ :=
  fun D θ hθ γ hγ => exists_GQ_of_unitary θ hθ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) γ hγ

end GlobalTheory.Core.Mi
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem exists_isDec_finM : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (g : GA D (D.sp.X 0)), ∃ p, GlobalTheory.AdForm.IsDec F.cls0.lev F.cls0.y (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g) p :=
  fun D _ F g => GlobalTheory.AdForm.Model.exists_dec (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) F.cls0.lev F.cls0.y F.cls0.y_bij.2 g

end GlobalTheory.Core.Mi
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.HdNc

theorem anti_of_step {r : ℕ} (f : Fin r → ℝ) (h : ∀ (i : Fin r) (hi : i.1 + 1 < r), f ⟨i.1 + 1, hi⟩ < f i) :
    ∀ a b : Fin r, a ≤ b → f b ≤ f a := by
  have key : ∀ (d a : ℕ) (ha : a + d < r), f ⟨a + d, ha⟩ ≤ f ⟨a, by omega⟩ := by
    intro d
    induction d with
    | zero => intro a ha; exact le_rfl
    | succ d ih =>
      intro a ha
      have h1 := h ⟨a + d, by omega⟩ (by simp only []; omega)
      have h2 := ih a (by omega)
      have e : (⟨(⟨a + d, by omega⟩ : Fin r).1 + 1, by simp only []; omega⟩ : Fin r) = ⟨a + (d + 1), ha⟩ := by
        ext; simp only []; omega
      rw [e] at h1
      linarith
  intro a b hab
  have hd := key (b.1 - a.1) a.1 (by omega)
  have e1 : (⟨a.1 + (b.1 - a.1), by omega⟩ : Fin r) = b := by ext; simp only []; omega
  rw [e1] at hd
  exact hd

theorem lamS_node (R : Ranks) (P : HCParam R) (j : ℕ) (hj : j < R.m) (hi : R.k - 1 + j < R.r) :
    lamS R P ⟨R.k - 1 + j, hi⟩ = -(((P.b ⟨j, hj⟩ : ℚ)) : ℝ) := by
  unfold lamS
  rw [dite_eq_right (by simp only []; omega)]
  have e : R.k - 1 + j - (R.k - 1) = j := by omega
  simp only [e, dif_pos hj]

theorem node_of_sign (R : Ranks) (a b : Fin R.r) (hab : a < b) (hne : epsS R a ≠ epsS R b) : R.k ≤ b.1 := by
  by_contra hb
  push_neg at hb
  apply hne
  have ha : a.1 < R.k - 1 := by
    have : a.1 < b.1 := hab
    omega
  unfold epsS
  rw [if_pos ha]
  by_cases h1 : b.1 < R.k - 1
  · rw [if_pos h1]
  · rw [if_neg h1]
    have : b.1 - (R.k - 1) = 0 := by omega
    simp [this]

theorem gap_lt {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (H : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (τ : D.what₂.Tau) (a b : Fin D.R.r) (hab : a < b) (hne : epsS D.R a ≠ epsS D.R b) :
    Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤ lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) b := by
  have hkb := node_of_sign D.R a b hab hne
  have hbr : b.1 < D.R.r := b.2
  have hm2 := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hgap := GlobalTheory.Core.Rk.HdGap.gap_of H τ (b.1 - D.R.k) (by omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlam, -, -, hCl⟩ := H
  have hstep : ∀ (i : Fin D.R.r) (hi : i.1 + 1 < D.R.r),
      lamS D.R (D.hc τ) ⟨i.1 + 1, hi⟩ < lamS D.R (D.hc τ) i := by
    intro i hi
    have := hlam τ i hi
    have h0 : (0 : ℝ) ≤ Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 + (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by positivity
    linarith
  set j := b.1 - D.R.k with hj
  have hj1 : j + 1 < D.R.m := by omega
  have e1 : b = ⟨D.R.k - 1 + (j + 1), by omega⟩ := by ext; simp only []; omega
  have hc : (⟨D.R.k - 1 + j, by omega⟩ : Fin D.R.r) ≤ b := by
    rw [Fin.le_def]; simp only []; omega
  have hac : a ≤ (⟨D.R.k - 1 + j, by omega⟩ : Fin D.R.r) := by
    rw [Fin.le_def]; simp only []; have : a.1 < b.1 := hab; omega
  have h1 := anti_of_step _ hstep _ _ hac
  have h2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤
      (((D.hc τ).b ⟨j + 1, hj1⟩ : ℚ) : ℝ) - (((D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := hgap
  rw [lamS_node D.R (D.hc τ) j (by omega) (by omega)] at h1
  rw [e1, lamS_node D.R (D.hc τ) (j + 1) hj1 (by omega)]
  linarith

theorem hd_nc : ∃ Cl₀ : ℝ, ∀ (D : D7) (L C' Cl Cg cb Cu cT CT : ℝ), Cl₀ ≤ Cl → HD D L C' Cl Cg cb Cu cT CT →
    ∀ X : Formalism.L2.SG.HidaSetting.HidaSetting D, GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) := by
  refine ⟨1801, fun D L C' Cl Cg cb Cu cT CT hCl H X => ?_⟩
  have HL := H.2.2.1
  obtain ⟨hS, hr⟩ := GlobalTheory.Core.Rk.HdGap.scale_of hCl HL
  have hr1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast (show 1 ≤ D.R.r by omega)
  have h4 : 100 * (D.R.r : ℝ) ^ 4 ≤ 1801 * (D.R.r : ℝ) ^ 19 := by
    have : (D.R.r : ℝ) ^ 4 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hr1 (by norm_num)
    have : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 4 := by positivity
    linarith
  have key : ∀ (τ : D.what₂.Tau) (a b : Fin D.R.r), epsS D.R a ≠ epsS D.R b →
      100 * (D.R.r : ℝ) ^ 4 ≤ |lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) b| := by
    intro τ a b hne
    have hp : (0 : ℝ) ≤ 100 * (D.R.r : ℝ) ^ 4 := by positivity
    rcases lt_trichotomy a b with h | h | h
    · have := gap_lt HL τ a b h hne
      rw [abs_of_nonneg (by linarith)]
      linarith
    · exact absurd (by rw [h]) hne
    · have := gap_lt HL τ b a h (Ne.symm hne)
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
  intro v a b hab
  rw [X.eps_eq, X.eps_eq] at hab
  rw [X.lam_eq, X.lam_eq]
  exact key _ _ _ hab

end GlobalTheory.Core.Rk.HdNc
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.SizeRowsRec

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare.SizeRows

theorem sizeRowsS_numRec : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word),
    SizeRowsS CY (numDatumOfParameters D L) (codeRec L u) := by
  intro D large₂ CY hR u
  have hnu := GlobalTheory.T.fockPartitionRows_numericDatum_mem_Icc D large₂ CY hR u
  obtain ⟨⟨P⟩, ⟨s2, s3, s4⟩, hg, ⟨s10, -, -, -, s14⟩, ⟨n, hn⟩, -⟩ := hR
  have hDel : ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del := by rw [hn, Nat.floor_natCast]
  have hSc : (numDatumOfParameters D large₂).Sc = large₂.Sc := by
    rw [large₂.Sc_eq]
    show (D.R.k : ℝ) * (4 * ((⌊D.s.Del⌋₊ : ℕ) : ℝ)) = _
    rw [← Rat.cast_natCast, ← Rat.cast_natCast (α := ℝ) ⌊D.s.Del⌋₊, hDel]
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hm : (0 : ℝ) < D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 0 < D.R.m)
  have hn0 : 0 < D.R.n := D.R.n_pos'
  have hq := D.host.hyp.1.pos
  have hd := D.host.hyp.2.1.pos
  refine ⟨⟨?_, ?_, ?_, s4, ?_⟩, fun i => ⟨?_, hg i⟩, trivial, f_mul_N_le_b P s10, hnu, ?_, ?_, ?_, ?_, ?_⟩
  · exact s2
  · refine log_le_L_of_le_cond P hq ?_
    unfold LevelStarExponents.condE
    exact le_trans (Nat.le_mul_of_pos_left _ D.host.QS_pos) (Nat.le_mul_of_pos_right _ hd)
  · refine log_le_L_of_le_cond P hd ?_
    unfold LevelStarExponents.condE
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos D.host.QS_pos hq)
  · rw [large₂.logDerivative_at_one_eq] at s3
    exact s3
  · obtain ⟨Y, h1, -, -, h2⟩ := P.g_Y
    exact h1.trans (h2 i).1
  · intro z i j
    refine (large₂.be_close (tauPl D z) i j).trans ?_
    show large₂.etaSz ≤ (D.R.m : ℝ) * ((⌈LevelStarExponents.h0 large₂⌉₊ : ℕ) : ℝ)
    have h := Nat.le_ceil (LevelStarExponents.h0 large₂)
    calc large₂.etaSz = (D.R.m : ℝ) * LevelStarExponents.h0 large₂ := by unfold LevelStarExponents.h0; field_simp
      _ ≤ _ := by gcongr
  · intro z i
    rw [hSc]
    obtain ⟨h1, h2⟩ := large₂.cloud_v (tauPl D z) i
    exact ⟨by exact_mod_cast h1, h2⟩
  · intro z i h1 h2
    obtain ⟨i, hi⟩ := i
    obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by simp only at h1; omega⟩
    have hl : l < D.R.k - 2 := by
      have : l + 1 + 1 < D.R.k := h2
      omega
    have e : (numDatumOfParameters D large₂).uW (codeRec large₂ u) z ⟨l + 1, hi⟩ = (D.hcW u (tauPl D z)).u ⟨l + 1, hi⟩ := by
      rw [D.s.u_letter u (tauPl D z) l hl, D.hcW_v]
      unfold NumDatum.uW
      rw [dite_eq_left ⟨h1, h2⟩]
      show _ - _ - (if D.s.letter u ⟨l, hl⟩ = true then ((⌊D.s.Del⌋₊ : ℕ) : ℚ) else 0) = _
      rw [hDel]
      rfl
    rw [hSc, e]
    obtain ⟨a1, a2⟩ := large₂.cloud_u u (tauPl D z) ⟨l + 1, hi⟩ h1 h2
    exact ⟨by exact_mod_cast a1, a2⟩
  · intro t ht
    have h := (large₂.top_u (tauPl D (false, t)) ⟨t, ht⟩ (by omega) (eTau_tauPl (false, t))).2
    have e : (((numDatumOfParameters D large₂).bT t : ℚ) : ℝ) = (large₂.bT ⟨t, ht⟩ : ℝ) := by
      unfold NumDatum.bT
      push_cast
      erw [h]
      ring
    rw [e]
    exact ⟨large₂.bT_ge _, s14 _⟩
  · intro z hz hk2
    have hz' := not_top_of z hz
    rw [hSc]
    refine ⟨P.uk_extreme _ hk2 hz', (large₂.cloud_gap _ (by omega) hz').1, ?_⟩
    have h1 := P.cloud_place_bound _ (by omega) hz'
    have h2 := (large₂.cloud_v (tauPl D z) ⟨0, by omega⟩).2
    push_cast at h1
    show (((D.hc (tauPl D z)).u ⟨0, by omega⟩ : ℚ) : ℝ) ≤ _
    linarith

end GlobalTheory.CoreHt.SizeRowsRec
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_realIntertwiner_ne_zero_KFinite_tensor : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank → (WO V W → ℂ)) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsItW θ M M' ω pt It → ∀ h' : GlobalTheory.Chain.IoLift.KSm M', ∃ φ y, It φ (GlobalTheory.Chain.IoLift.inclK h' y) ≠ 0 := by
  first | exact @GlobalTheory.Chain.IoLift.ItNe.exists_ne_zero_inclK | exact GlobalTheory.Chain.IoLift.ItNe.exists_ne_zero_inclK | (intros; apply GlobalTheory.Chain.IoLift.ItNe.exists_ne_zero_inclK <;> assumption)
end
