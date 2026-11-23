module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle219
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle167
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle224
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle186
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm


theorem _root_.GlobalTheory.T.residuePairStabilizer_keeps_integralLastCoordDiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m' m : ℕ) (hm : m' = m) (b b' : Matrix (Fin m') (Fin m') k), b * b' = 1 → b' * b = 1 →
    ∀ P : Pair k (Fin m'), (∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k]) →
    ∀ (c τ : k) (q : Unif k), valuation k τ = valuation k ((q.1 : 𝒪[k]) : k) → valuation k c = 1 →
    (∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m', r0.1 + 1 = m' →
      ∃ s : 𝒪[k], (s : k) = c * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s)) →
    ∀ g : GL (Fin m') k, g • P = P →
      (b * g.val * b').reindex (finCongr hm) (finCongr hm) * (b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm) = 1 ∧
      (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], u r0 = τ * s) ↔
        ((∀ r, ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r ∈ 𝒪[k]) ∧
          ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r0 = τ * s)) ∧
      (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔
        ∀ r, (((b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm))ᵀ *ᵥ u) r ∈ 𝒪[k]) := by
  first | exact @GlobalTheory.PairKeep.keep | exact GlobalTheory.PairKeep.keep | (intros; apply GlobalTheory.PairKeep.keep <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm


theorem _root_.GlobalTheory.T.unitary_keeps_baseLattice_of_split_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (φ : E ⊗[F] v.adicCompletion F →+* k),
    (∀ z, z ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring ↔
      φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR σ (v.adicCompletion F) z) ∈ 𝒪[k]) →
    ∀ (m : ℕ) (t : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin m → E)),
    (∀ x, x ∈ Λ ↔ ∀ j : Fin m, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = m → t ∣ r)) →
    ∀ q : Unif k, valuation k (φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E))) = valuation k ((q.1 : 𝒪[k]) : k) →
    valuation k (φ (Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)))) = 1 →
    ∀ M : GL (Fin m) (E ⊗[F] v.adicCompletion F), M ∈ Formalism.UG.UJ (Formalism.UG.sigR σ (v.adicCompletion F)) 1 →
    ∀ h h' : Matrix (Fin m) (Fin m) k, M.val.map φ = h → h * h' = 1 →
    (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], u r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s) ↔
      ((∀ r, (h *ᵥ u) r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], (h *ᵥ u) r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s)) →
    (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔ ∀ r, (h'ᵀ *ᵥ u) r ∈ 𝒪[k]) →
    M ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) Λ) := by
  first | exact @GlobalTheory.SplitStab.stab_of_split_components | exact GlobalTheory.SplitStab.stab_of_split_components | (intros; apply GlobalTheory.SplitStab.stab_of_split_components <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.compactAverage_thetaFamily_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (𝒢 : Set (K → WO S T → ℂ)), (∀ F ∈ 𝒢, Continuous fun p : K × WO S T => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, IsThetaFunO ψ S T (F k)) → (∀ F ∈ 𝒢, ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) ∈ 𝒢) → ∀ F ∈ 𝒢, ∀ (n : ℕ) (L : (Fin n → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => ∫ k, F k (w + L t) ∂μ := by
  first | exact @GlobalTheory.ThetaAvgSmooth.avg_smooth | exact GlobalTheory.ThetaAvgSmooth.avg_smooth | (intros; apply GlobalTheory.ThetaAvgSmooth.avg_smooth <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

noncomputable section

namespace GlobalTheory.Core.SBesLevi

variable {D : D7}

theorem bridge_fix (D : D7) (g : GA D (D.sp.Y 0)) (x : Fin (Formalism.L2.SG.InstExistsPf.instOf D).n → (Formalism.L2.SG.InstExistsPf.instOf D).E) :
    (mt (D.sp.Y 0) g *ᵥ (fun k => incA D (x k)) = fun k => incA D (x k)) ↔
    ((∀ v, uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) *ᵥ rv (Formalism.L2.SG.InstExistsPf.instOf D) v x = rv (Formalism.L2.SG.InstExistsPf.instOf D) v x) ∧
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 *ᵥ incl (Formalism.L2.SG.InstExistsPf.instOf D) x = incl (Formalism.L2.SG.InstExistsPf.instOf D) x) := by
  have hb := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D g)
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D g) = g :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply g
  have hb1 : ∀ v, uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) = ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) g v :=
    fun v => (hb.1 v).trans (congrArg (fun q => ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) q v) key)
  have hb2 : (Formalism.IndefR.RationalEmbedding.inst D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) g :=
    hb.2.trans (congrArg (fun q => ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) q) key)
  have hdet : ∀ v, IsUnit ((Formalism.L2.SG.InstExistsPf.instOf D).P v).det :=
    fun v => (Matrix.isUnit_iff_isUnit_det _).1 ((Formalism.L2.SG.InstExistsPf.instOf D).P_unit v)
  have hinf : ∀ v, (uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) *ᵥ rv (Formalism.L2.SG.InstExistsPf.instOf D) v x = rv (Formalism.L2.SG.InstExistsPf.instOf D) v x) ↔
      ∀ i, thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) =
        thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v (incA D (x i)) := by
    intro v
    have hθ : (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g).map (thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v) *ᵥ
        (fun i => (Formalism.L2.SG.InstExistsPf.instOf D).φ v (x i)) =
        fun i => thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) := by
      funext i
      refine Eq.trans ?_ (RingHom.map_mulVec (thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v) (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g) (fun k => incA D (x k)) i).symm
      congr 1
      funext k
      exact (GlobalTheory.Core.SBesFlagTie.thetaV_incA v (x k)).symm
    have hφ : (fun i => (Formalism.L2.SG.InstExistsPf.instOf D).φ v (x i)) =
        fun i => thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v (incA D (x i)) :=
      funext fun i => (GlobalTheory.Core.SBesFlagTie.thetaV_incA v (x i)).symm
    rw [hb1 v]
    unfold ofHAInf rv
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet v), Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hθ, hφ]
    constructor
    · intro h i
      have := congrArg (fun w => (Formalism.L2.SG.InstExistsPf.instOf D).P v *ᵥ w) h
      simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hdet v), Matrix.one_mulVec] at this
      exact congrFun this i
    · intro h
      rw [funext h]
  have hfin : ((Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 *ᵥ incl (Formalism.L2.SG.InstExistsPf.instOf D) x =
      incl (Formalism.L2.SG.InstExistsPf.instOf D) x) ↔
      ∀ i, tauF (Formalism.L2.SG.InstExistsPf.instOf D) ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) =
        tauF (Formalism.L2.SG.InstExistsPf.instOf D) (incA D (x i)) := by
    have hτ : (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g).map (tauF (Formalism.L2.SG.InstExistsPf.instOf D)) *ᵥ
        incl (Formalism.L2.SG.InstExistsPf.instOf D) x =
        fun i => tauF (Formalism.L2.SG.InstExistsPf.instOf D) ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) := by
      funext i
      refine Eq.trans ?_ (RingHom.map_mulVec (tauF (Formalism.L2.SG.InstExistsPf.instOf D)) (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g) (fun k => incA D (x k)) i).symm
      congr 1
      funext k
      exact (GlobalTheory.Core.SBesFlagTie.tauF_incA (x k)).symm
    have hi : incl (Formalism.L2.SG.InstExistsPf.instOf D) x = fun i => tauF (Formalism.L2.SG.InstExistsPf.instOf D) (incA D (x i)) :=
      funext fun i => (GlobalTheory.Core.SBesFlagTie.tauF_incA (x i)).symm
    have e1 := hb2
    unfold ofHAFin at e1
    change (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = _ at e1
    rw [e1, hτ, hi]
    exact funext_iff
  rw [hfin, forall_congr' hinf]
  change ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) = fun k => incA D (x k)) ↔ _
  constructor
  · intro h
    exact ⟨fun v i => by rw [congrFun h i], fun i => by rw [congrFun h i]⟩
  · rintro ⟨h1, h2⟩
    funext i
    have := Formalism.L2.SG.Pf.TT_ext (Formalism.L2.SG.InstExistsPf.instOf D)
      ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i - (show AF (Formalism.L2.SG.InstExistsPf.instOf D).F ⊗[(Formalism.L2.SG.InstExistsPf.instOf D).F] (Formalism.L2.SG.InstExistsPf.instOf D).E from incA D (x i)))
      (fun v => by rw [map_sub, h1 v i, sub_self]) (by rw [map_sub, h2 i, sub_self])
    exact sub_eq_zero.1 this

theorem transport_fix (D : D7) (I : AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n) (S : Set (Fin I.n → I.E))
    (s : (Formalism.L2.SG.InstExistsPf.instOf D).GA) :
    ((castGA hI.symm s).1 ∈ Formalism.L2.SG.PoincareInHH.HinfS I S ∧ (castGA hI.symm s).2 ∈ Formalism.L2.SG.PoincareInHH.HfinS I S) ↔
    ∀ p ∈ S, (∀ v, uMat (s.1 v) *ᵥ rv (Formalism.L2.SG.InstExistsPf.instOf D) v (fun k => ιE (p (Fin.cast hr k))) =
        rv (Formalism.L2.SG.InstExistsPf.instOf D) v (fun k => ιE (p (Fin.cast hr k)))) ∧
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat s.2 *ᵥ incl (Formalism.L2.SG.InstExistsPf.instOf D) (fun k => ιE (p (Fin.cast hr k))) =
        incl (Formalism.L2.SG.InstExistsPf.instOf D) (fun k => ιE (p (Fin.cast hr k))) := by
  generalize hI.symm = e
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hv : ∀ p : Fin (Formalism.L2.SG.InstExistsPf.instOf D).n → (Formalism.L2.SG.InstExistsPf.instOf D).E,
      (fun k : Fin (Formalism.L2.SG.InstExistsPf.instOf D).n => ιE (p (Fin.cast hr k))) = p := fun p => funext fun k => by rw [hid]; rfl
  rw [GlobalTheory.Core.SBesFlagTie.castGA_self]
  change ((∀ v, ∀ x ∈ S, uMat (s.1 v) *ᵥ rv _ v x = rv _ v x) ∧ (∀ y ∈ S, _)) ↔ _
  constructor
  · rintro ⟨h1, h2⟩ p hp
    rw [hv p]
    exact ⟨fun v => h1 v p hp, h2 p hp⟩
  · intro H
    refine ⟨fun v p hp => ?_, fun p hp => ?_⟩
    · have := (H p hp).1 v
      rw [hv p] at this
      exact this
    · have := (H p hp).2
      rw [hv p] at this
      exact this

theorem fix_smul {S : HSp D} (g : GA D S) {c : D.host.E} (hc : c ≠ 0) (y : Fin S.rank → D.host.E) :
    (mt S g *ᵥ (fun k => incA D ((c • y) k)) = fun k => incA D ((c • y) k)) ↔
      (mt S g *ᵥ (fun k => incA D (y k)) = fun k => incA D (y k)) := by
  have hs : (fun k => incA D ((c • y) k)) = incA D c • fun k => incA D (y k) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  have hu : IsUnit (incA D c) := (IsUnit.mk0 c hc).map (incA D)
  rw [hs, Matrix.mulVec_smul]
  exact hu.smul_left_cancel

theorem fix_cols {S : HSp D} (g : GA D S) {ρ : ℕ} (e : Matrix (Fin S.rank) (Fin ρ) D.host.E) :
    mt S g ⬝ rat e = rat e ↔ ∀ a, (mt S g *ᵥ (fun k => incA D (e k a)) = fun k => incA D (e k a)) := by
  constructor
  · intro h a
    funext k
    exact congrFun (congrFun h k) a
  · intro h
    funext k a
    exact congrFun (h a) k

theorem rat_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (w : Fin n → D.host.E) :
    (fun k => incA D ((M *ᵥ w) k)) = rat M *ᵥ fun k => incA D (w k) := by
  funext k
  exact RingHom.map_mulVec (incA D) M w k

theorem range_embA_iff {S V₀ A L : HSp D} {ρ : ℕ} (d : HypDec S V₀ ρ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E)
    (hζ : IsLineVec L ζ) (g : GA D S) :
    g ∈ (embA d o).range ↔ (mt S g ⬝ d.jX = d.jX ∧ mt S g ⬝ d.jY = d.jY ∧
      (mt S g *ᵥ (fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k)) = fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k))) := by
  have hw : (fun k => incA D (vecB o ζ k)) = o.jB *ᵥ fun k => incA D (ζ k) := rat_mulVec o.iB ζ
  rw [rat_mulVec d.i₀ (vecB o ζ)]
  change _ ↔ (_ ∧ _ ∧ mt S g *ᵥ (d.j0 *ᵥ _) = d.j0 *ᵥ _)
  constructor
  · rintro ⟨a, rfl⟩
    change mt S (d.emb0 (o.emb (a, 1))) ⬝ d.jX = d.jX ∧ mt S (d.emb0 (o.emb (a, 1))) ⬝ d.jY = d.jY ∧
      mt S (d.emb0 (o.emb (a, 1))) *ᵥ (d.j0 *ᵥ _) = d.j0 *ᵥ _
    refine ⟨d.wittDecomp_anisotropicEmbedding_inclX _, d.wittDecomp_anisotropicEmbedding_inclY _, ?_⟩
    rw [Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_mulVec (M := mt V₀ _), o.emb_jB,
      MixModel.mt_one, Matrix.mul_one]
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨b, rfl⟩ := GlobalTheory.T.exists_levi_preimage_of_fix_isotropic_frames d g h1 h2
    have hb : (mt V₀ b *ᵥ fun k => incA D (vecB o ζ k)) = fun k => incA D (vecB o ζ k) := by
      rw [Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec] at h3
      have := congrArg (fun w => d.p0 *ᵥ w) h3
      simp only [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec] at this
      simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, d.p0_j0, Matrix.one_mul] using this
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_orthogonalComplement_preimage_of_fix_line o ζ hζ b hb
    exact ⟨a, by rw [← ha]; rfl⟩

theorem range_embA_eq_H : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → _root_.GlobalTheory.Core.Mi.IdE X → ∀ (V₀ L : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ (D.sp.X 0) L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → d.e = GlobalTheory.Core.SBesEx.eM X h t lam → d.e' = GlobalTheory.Core.SBesEx.e'M X h t lam → d.i₀ *ᵥ vecB o ζ = t • GlobalTheory.Core.SBesEx.cY X h (X.zu u) → ∀ g, g ∈ (embA d o).range ↔ (iotaX X h g).1 ∈ Hinf X u ∧ (iotaX X h g).2 ∈ Hfin X u := by
  intro D X h u t lam ht hl hId V₀ L d o ζ hζ he he' hz g
  have hsc : ∀ a, GlobalTheory.Core.SBesEx.scl t lam a ≠ 0 := fun a => mul_ne_zero ht (pow_ne_zero _ hl)
  have hR : ((iotaX X h g).1 ∈ Hinf X u ∧ (iotaX X h g).2 ∈ Hfin X u) ↔
      ∀ p ∈ fixSet X u, (mt (D.sp.Y 0) g *ᵥ (fun k => incA D (X.ιE (p (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (p (Fin.cast (rank_eq X h) k)))) :=
    (transport_fix D X.B.I X.ιE hId h (rank_eq X h) (fixSet X u) (Formalism.IndefR.RationalEmbedding.iota D g)).trans
      (forall₂_congr fun p _ => (bridge_fix D g _).symm)
  rw [range_embA_iff d o ζ hζ g, hR, HypDec.jX, HypDec.jY, fix_cols, fix_cols]
  change _ ↔ ∀ p ∈ Set.range X.eR ∪ Set.range X.fR ∪ {X.zR u}, _
  have hE : ∀ a, (fun k => d.e k a) = GlobalTheory.Core.SBesEx.scl t lam a • GlobalTheory.Core.SBesEx.cY X h (X.eX a) := by
    intro a; funext k; rw [he]; rfl
  have hE' : ∀ a, (fun k => d.e' k a) = (star (GlobalTheory.Core.SBesEx.scl t lam a))⁻¹ • GlobalTheory.Core.SBesEx.cY X h (X.fY a) := by
    intro a; funext k; rw [he']; rfl
  have hA : ∀ a, ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (d.e k a)) = fun k => incA D (d.e k a)) ↔
      ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (X.ιE (X.eR a (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (X.eR a (Fin.cast (rank_eq X h) k)))) := fun a => by
    have := fix_smul g (hsc a) (GlobalTheory.Core.SBesEx.cY X h (X.eX a))
    rw [← hE a] at this
    exact this
  have hB : ∀ a, ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (d.e' k a)) = fun k => incA D (d.e' k a)) ↔
      ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (X.ιE (X.fR a (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (X.fR a (Fin.cast (rank_eq X h) k)))) := fun a => by
    have := fix_smul g (inv_ne_zero (star_ne_zero.2 (hsc a))) (GlobalTheory.Core.SBesEx.cY X h (X.fY a))
    rw [← hE' a] at this
    exact this
  have hC : ((mt (D.sp.Y 0) g *ᵥ fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k)) = fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k)) ↔
      ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (X.ιE (X.zR u (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (X.zR u (Fin.cast (rank_eq X h) k)))) := by
    have := fix_smul g ht (GlobalTheory.Core.SBesEx.cY X h (X.zu u))
    rw [← hz] at this
    exact this
  simp only [hA, hB, hC]
  constructor
  · rintro ⟨h1, h2, h3⟩ p hp
    rcases hp with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hp
    · exact h1 a
    · exact h2 a
    · rw [Set.mem_singleton_iff] at hp
      subst hp
      exact h3
  · intro H
    exact ⟨fun a => H _ (Or.inl (Or.inl ⟨a, rfl⟩)), fun a => H _ (Or.inl (Or.inr ⟨a, rfl⟩)), H _ (Or.inr rfl)⟩

end GlobalTheory.Core.SBesLevi

end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix


theorem _root_.GlobalTheory.T.doubled_lagrangian_transverse_in_open_orbit : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → (∀ x : Fin V.rank → D.host.E, diagSnd γi *ᵥ x = 0 → x = 0) → ∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V := by
  first | exact @GlobalTheory.Core.Rk.Dich.exists_mem_siegel_of_diagSnd | exact GlobalTheory.Core.Rk.Dich.exists_mem_siegel_of_diagSnd | (intros; apply GlobalTheory.Core.Rk.Dich.exists_mem_siegel_of_diagSnd <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix


theorem _root_.GlobalTheory.T.rational_isometry_keeps_isotropic_frame_of_siegel : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → ∀ (r : ℕ) (K : Matrix (Fin V.rank) (Fin r) D.host.E), diagSnd γi * K = 0 → (∀ x : Fin V.rank → D.host.E, diagSnd γi *ᵥ x = 0 → ∃ y, x = K *ᵥ y) → IsIsoFrame V (leviMat finSumFinEquiv γi * K) → ∀ δ ∈ GQ V, ∀ δ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, (matHom V δ).1 = δ₀.map (incA D) → γ * io V (δ, 1) * γ⁻¹ ∈ siegel V → ∃ G : Matrix (Fin r) (Fin r) D.host.E, IsUnit G ∧ δ₀ * (leviMat finSumFinEquiv γi * K) = leviMat finSumFinEquiv γi * K * G := by
  first | exact @GlobalTheory.Core.Rk.Dich.isoFrame_keep | exact GlobalTheory.Core.Rk.Dich.isoFrame_keep | (intros; apply GlobalTheory.Core.Rk.Dich.isoFrame_keep <;> assumption)
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

noncomputable section

namespace GlobalTheory.NrmVol

theorem phiQ_mul_conj_eq_indicator : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ) (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ x : Matrix (Fin b) (Fin a) (Fv D.host.F v), phiQ v r mu x * (starRingEnd ℂ) (phiQ v r mu x) = (GlobalTheory.NrmVol.suppQ v r).indicator (fun _ => (1 : ℂ)) x := by
  intro D PP v φ hP a b r ξ mu hL x
  by_cases hx : x ∈ GlobalTheory.NrmVol.suppQ v r
  · rw [Set.indicator_of_mem hx]
    have h : IsUnit (topL r x).det ∧ Valued.v (topL r x).det = 1 ∧
        (∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F) ∧
        ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1 := hx
    unfold phiQ
    rw [dite_eq_left h]
    obtain ⟨⟨red, -, -, hrel, -⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hP
    set u := h.1.unit with hu
    have hv : Valued.v (u : Fv D.host.F v) = 1 := by rw [hu, IsUnit.unit_spec]; exact h.2.1
    have hvi : Valued.v ((u⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
    have hint : (u : Fv D.host.F v) ∈ v.adicCompletionIntegers D.host.F :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hv.le
    have hint' : ((u⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v) ∈ v.adicCompletionIntegers D.host.F :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hvi.le
    have hunit : IsUnit (⟨(u : Fv D.host.F v), hint⟩ : v.adicCompletionIntegers D.host.F) :=
      ⟨⟨⟨_, hint⟩, ⟨_, hint'⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩, rfl⟩
    haveI : Finite (kP PP) := PP.asIdeal.finiteQuotientOfFreeOfNeBot PP.ne_bot
    set k := (hunit.map red).unit with hk
    have hR : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (u : Fv D.host.F v) (k : kP PP) :=
      (hrel _ _).2 ⟨hint, (IsUnit.unit_spec (hunit.map red)).symm⟩
    have hmu : mu u = ξ k := hL u k hR
    haveI : Finite (kP PP)ˣ := Finite.of_injective _ Units.val_injective
    obtain ⟨n, hn0, hn⟩ := (ξ.isOfFinOrder (isOfFinOrder_of_finite k)).exists_pow_eq_one
    have hpow : ((mu u : ℂˣ) : ℂ) ^ n = 1 := by
      rw [hmu, ← Units.val_pow_eq_pow_val, hn, Units.val_one]
    have hnorm : ‖((mu u : ℂˣ) : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow hn0.ne'
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_inv, hnorm]
    norm_num
  · rw [Set.indicator_of_notMem hx, phiQ_eq_zero_of_not_mem v r mu x hx, zero_mul]

end GlobalTheory.NrmVol
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem restrModel_isPlaceModel : ∀ (D : D7) {m n m' n' m'' n'' : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (BS : Mx D m n → Mx D m n → AF D.host.F) (hsS : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (BA : Mx D m' n' → Mx D m' n' → AF D.host.F) (hsA : Mx D m' n' → (Mx D m' n' → ℂ) → (Mx D m' n' → ℂ)) (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (e : AE D) (ΛS : AddSubgroup (Mx D m n)) (ΛA : AddSubgroup (Mx D m' n')) (h : Mx D m'' n'' → ℂ) (f₀ : Mx D m n → ℂ) (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)), IsPlaceModel ψ BS hsS e ΛS 1 f₀ T' → (∀ a F w y, hsS (r.symm (a, 0)) F (r.symm (w, y)) = hsA a (fun w' => F (r.symm (w', y))) w) → (∀ t a, BS t (r.symm (a, 0)) = BA (r t).1 a) → (∀ a, IsHalf e a → IsHalf e (r.symm (a, 0))) → (∀ a, IsHalf (cA D e) a → IsHalf (cA D e) (r.symm (a, 0))) → (∀ Φ, IsSBHalf e ΛA Φ → IsSBHalf e ΛS (fun t => Φ (r t).1 * h (r t).2)) → halfInd e ΛS = (fun t => halfInd e ΛA (r t).1 * h (r t).2) → ∀ y, IsPlaceModel ψ BA hsA e ΛA 1 (fun w => f₀ (r.symm (w, y))) (GlobalTheory.FinPl.ExtZero.restrModel r h T' y) := by
  intro D m n m' n' m'' n'' ψ BS hsS BA hsA r e ΛS ΛA h f₀ T' hT hcomp hB hhalf hhalfc hSB hInd y
  refine ⟨?_, ?_, ?_⟩
  · intro Φ hΦ x hx
    funext w
    rw [restrModel_apply]
    have hfun : (fun t => (fun t => Φ (t + x)) (r t).1 * h (r t).2) =
        fun t => (fun t => Φ (r t).1 * h (r t).2) (t + r.symm (x, 0)) := by
      funext t
      simp only [map_add (f := _), AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, add_zero]
    rw [hfun, hT.trans _ (hSB Φ hΦ) _ (hhalf x hx), hcomp]
    rfl
  · intro Φ hΦ y' hy'
    funext w
    rw [restrModel_apply]
    have hfun : (fun t => (fun t => ψ (BA t y') * Φ t) (r t).1 * h (r t).2) =
        fun t => ψ (BS t (r.symm (y', 0))) * (fun t => Φ (r t).1 * h (r t).2) t := by
      funext t
      simp only [hB, mul_assoc]
    rw [hfun, hT.modul _ (hSB Φ hΦ) _ (hhalfc y' hy'), hcomp]
    rfl
  · funext w
    rw [restrModel_apply]
    have hfun : (fun t => ((1 : ℂ) • halfInd e ΛA) (r t).1 * h (r t).2) = (1 : ℂ) • halfInd e ΛS := by
      rw [hInd]; funext t; simp
    rw [hfun, hT.vac]

end GlobalTheory.FinPl.ExtZero
end
end
