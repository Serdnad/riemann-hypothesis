module

public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle008
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle026
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LeftInvOfUnitary
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle839
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle782
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle149
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle208
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle332
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisConjTorsionTranslatesOddThetaProduct
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackFirstGroupRationalPointEqSmul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackSecondGroupRationalPointEqDetSmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

noncomputable section

namespace GlobalTheory.DecompCompare

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Group

variable {G : Type} [Group G] (Γ K : Subgroup G)

end Group

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

end Stab

theorem frame_inv {n P Q : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature G P Q)
    {A : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ} (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) :
    ∃ L : Matrix (Fin n) (Fin P ⊕ Fin Q) ℂ, L * A = 1 ∧ A * L = 1 := by
  obtain ⟨A₀, L₀, h0, hl, hr⟩ := GlobalTheory.VolPairExists.exists_frame h
  obtain ⟨e, -⟩ := h
  have h1 : (L₀ * Formalism.UG.Jpq P Q * L₀ᴴ * Aᴴ * Formalism.UG.Jpq P Q) * A = 1 := by
    calc (L₀ * Formalism.UG.Jpq P Q * L₀ᴴ * Aᴴ * Formalism.UG.Jpq P Q) * A
        = L₀ * Formalism.UG.Jpq P Q * L₀ᴴ * (Aᴴ * Formalism.UG.Jpq P Q * A) := by simp only [Matrix.mul_assoc]
      _ = L₀ * Formalism.UG.Jpq P Q * (A₀ * L₀)ᴴ * Formalism.UG.Jpq P Q * A₀ := by
          rw [hA, ← h0, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = L₀ * (Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q) * A₀ := by
          rw [hr, Matrix.conjTranspose_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [GlobalTheory.VolPairExists.jpq_mul_self, Matrix.mul_one, hl]
  exact ⟨_, h1, (Matrix.mul_eq_one_comm_of_equiv e).1 h1⟩

variable (D : D7)

theorem KSub_eq (W : HSpace D.host.E) (hW : W.SigOK) {P Q : ℕ} (hs : ∀ τ, W.sig τ = (P, Q))
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ))
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ)
    (hA : ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) :
    KSub D W P Q θ A = levelW D.sp.cm W := by
  ext h
  refine ⟨fun hh => hh.1, fun hh => ⟨hh, fun ρ => ?_⟩⟩
  have hsig : Formalism.UG.HasSignature (W.gram.map (embOf D ρ)) P Q := by
    have := hW (embOf D ρ)
    rwa [hs] at this
  obtain ⟨L, hl, hr⟩ := frame_inv hsig (hA ρ)
  have hu : (infMat D.sp.cm.sig W.gram (θ ρ) h)ᴴ * W.gram.map (embOf D ρ) * infMat D.sp.cm.sig W.gram (θ ρ) h =
      W.gram.map (embOf D ρ) := GlobalTheory.FockCompare.RealAction.infMat_mem_UH (D := D) (θ := θ) hθ W h ρ
  refine ⟨GlobalTheory.VolPairExists.mkU _ (GlobalTheory.VolPairExists.conj_unitary (hA ρ) hr hu), Set.mem_univ _, ?_⟩
  rw [GlobalTheory.VolPairExists.mat_mkU, Matrix.mul_assoc, hl, Matrix.mul_one]

theorem exists_data (W : HSpace D.host.E) (hW : W.SigOK) {P Q : ℕ} (hs : ∀ τ, W.sig τ = (P, Q)) :
    (∃ θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) ∧
    ∃ A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ,
      ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ) := by
  refine ⟨GlobalTheory.DualPairCompare.exists_infFam D, ?_⟩
  have hsig : ∀ ρ, Formalism.UG.HasSignature (W.gram.map (embOf D ρ)) P Q := fun ρ => by
    have := hW (embOf D ρ)
    rwa [hs] at this
  choose A L hA _ using fun ρ => GlobalTheory.VolPairExists.exists_frame (hsig ρ)
  exact ⟨A, hA⟩

theorem isOpen_levelW (W : HSpace D.host.E) :
    IsOpen (levelW D.sp.cm W : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) :=
  GlobalTheory.StabOpen.isOpen_stab_latHat D W

end GlobalTheory.DecompCompare
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.TowerDrop

theorem archimedeanRallisFourth_of_discreteSeriesBlattner : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFourth X := by
  intro X _ _ hD h5
  refine ⟨fun t al be ga de hd i hi hr hs MM f hf => ?_,
    fun t al be ga de hd i hi hr hs MM f hf => ?_⟩
  · exact ((GlobalTheory.LowerTower.no_map_lower X hD h5 t al be ga de hd.1 i hi).1 hr hs) MM f hf
  · have hA := hd.1
    have ht : 1 ≤ t := hA.1
    have hn : 1 ≤ al.length + be.length + ga.length + de.length := hA.2.1
    have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg t
    obtain ⟨-, hpar, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
    obtain ⟨-, -, hsign, -⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hA
    have hno := (GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi).2.1 hr hs
    refine GlobalTheory.LowerTower.tensNo_first X hD h5 (by omega) _ hpar 0 ?_ hno MM f hf
    rw [GlobalTheory.SmallerSource.cPair_sub hr hs]
    refine fun a => ⟨(hsign a).1, fun h => (hsign a).2 (lt_of_le_of_ne h fun h0 => ?_)⟩
    have := hA.2.2.2.2.2.2.2.2.2.2 _ (GlobalTheory.LowerTower.lamA_mem al be ga de a)
    rw [h0, abs_zero] at this
    linarith

end GlobalTheory.TowerDrop
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.pAdicFrobeniusStickelberger_of_d7_datum : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicFrobeniusStickelberger D := by
  first | exact @GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula | exact GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula | (intros; apply GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.galois_conj_torsionTranslates_oddThetaProduct : ∀ D : D7, galB D := by
  first | exact @GlobalTheory.ProdThetaConj.galB_all | exact GlobalTheory.ProdThetaConj.galB_all | (intros; apply GlobalTheory.ProdThetaConj.galB_all <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaPullback_firstGroup_rationalPoint_eq_smul : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even N → Even N' → ∀ th ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (γA : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), IsRat D (γA : GL (Fin N) (AE D)) γ → (1 - γ).det ≠ 0 → Moves D (γA : GL (Fin N) (AE D)) L₁ → pull D (tor0 D cc δ) γ 1 th = (∏ τ, embT D τ γ.det ^ (-((N' / 2 : ℕ) : ℤ))) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ (stdL D N')) th := by
  first | exact @GlobalTheory.RatRow.pull_eq_smul_iop | exact GlobalTheory.RatRow.pull_eq_smul_iop | (intros; apply GlobalTheory.RatRow.pull_eq_smul_iop <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaPullback_secondGroup_rationalPoint_eq_det_smul : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even N → Even N' → ∀ th ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (γA' : GA D N') (γ' : Matrix (Fin N') (Fin N') D.host.E) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsRat D (γA' : GL (Fin N') (AE D)) γ' → (1 - γ').det ≠ 0 → Moves D (γA' : GL (Fin N') (AE D)) L₁' → pull D (tor0 D cc δ) 1 γ' th = (∏ τ, embT D τ γ'.det ^ (N / 2)) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) (stdL D N) L₁') th := by
  first | exact @GlobalTheory.RatEqui.pull_right_eq_det_smul | exact GlobalTheory.RatEqui.pull_right_eq_det_smul | (intros; apply GlobalTheory.RatEqui.pull_right_eq_det_smul <;> assumption)
end
