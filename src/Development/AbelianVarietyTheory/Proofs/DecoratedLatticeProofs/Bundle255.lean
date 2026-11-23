module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle202
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle225
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.weilOperator_integral_comm_of_bounded_finiteMeasure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (Ω : Type) [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω] (m : Measure Ω) [IsFiniteMeasure m] (F : Ω → WO S T → ℂ) (p : GA D S × GA D T), (∀ a, IsThetaFunO ψ S T (F a)) → (Continuous fun q : Ω × WO S T => F q.1 q.2) → (∃ C : ℝ, ∀ a x, ‖F a x‖ ≤ C) → (Continuous fun q : Ω × WO S T => om p (F q.1) q.2) → (∃ C : ℝ, ∀ a x, ‖om p (F a) x‖ ≤ C) → IsThetaFunO ψ S T (fun x => ∫ a, F a x ∂m) → ∀ x, om p (fun y => ∫ a, F a y ∂m) x = ∫ a, om p (F a) x ∂m := by
  first | exact @GlobalTheory.CommIntBdd.om_integral_comm_bdd | exact GlobalTheory.CommIntBdd.om_integral_comm_bdd | (intros; apply GlobalTheory.CommIntBdd.om_integral_comm_bdd <;> assumption)
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
open GlobalTheory.Core.Rk.SumBox

noncomputable section

namespace GlobalTheory.Core.Rk.SumBox


open Matrix ComplexOrder in
theorem isCartanInv_blockSum {k k₁ k₂ : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (GW : Matrix (Fin k₁) (Fin k₁) ℂ)
    (GH : Matrix (Fin k₂) (Fin k₂) ℂ) (iW : Matrix (Fin k) (Fin k₁) ℂ) (iH : Matrix (Fin k) (Fin k₂) ℂ)
    (pW : Matrix (Fin k₁) (Fin k) ℂ) (pH : Matrix (Fin k₂) (Fin k) ℂ) (sW : Matrix (Fin k₁) (Fin k₁) ℂ)
    (sH : Matrix (Fin k₂) (Fin k₂) ℂ) (hGh : Gᴴ = G) (hWW : iWᴴ * G * iW = GW) (hHH : iHᴴ * G * iH = GH)
    (hHW : iHᴴ * G * iW = 0) (h1 : pW * iW = 1) (h2 : pW * iH = 0) (h3 : pH * iH = 1) (h4 : pH * iW = 0)
    (hsum : iW * pW + iH * pH = 1) (hW : IsCartanInv GW sW) (hH : IsCartanInv GH sH) :
    IsCartanInv G (iW * sW * pW + iH * sH * pH) := by
  have hWH : iWᴴ * G * iH = 0 := by
    have := congrArg Matrix.conjTranspose hHW
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hGh, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have c1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), pW * (iW * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have c2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), pW * (iH * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.zero_mul]
  have c3 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), pH * (iH * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  have c4 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), pH * (iW * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, h4, Matrix.zero_mul]
  have g1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iWᴴ * (G * (iW * X)) = GW * X := fun X => by
    simp only [← Matrix.mul_assoc, hWW]
  have g2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iWᴴ * (G * (iH * X)) = 0 := fun X => by
    simp only [← Matrix.mul_assoc, hWH, Matrix.zero_mul]
  have g3 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iHᴴ * (G * (iH * X)) = GH * X := fun X => by
    simp only [← Matrix.mul_assoc, hHH]
  have g4 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iHᴴ * (G * (iW * X)) = 0 := fun X => by
    simp only [← Matrix.mul_assoc, hHW, Matrix.zero_mul]

  have hG : G = pWᴴ * GW * pW + pHᴴ * GH * pH := by
    calc G = (iW * pW + iH * pH)ᴴ * G * (iW * pW + iH * pH) := by
            rw [hsum, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by
        simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, g1, g2,
          g3, g4, Matrix.mul_zero, add_zero, zero_add]
  have hGs : G * (iW * sW * pW + iH * sH * pH) = pWᴴ * (GW * sW) * pW + pHᴴ * (GH * sH) * pH := by
    rw [hG]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, c1, c2, c3, c4, Matrix.mul_zero, add_zero, zero_add]
  have d1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iWᴴ * (pWᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, h1, conjTranspose_one, Matrix.one_mul]
  have d2 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iHᴴ * (pWᴴ * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, h2, conjTranspose_zero, Matrix.zero_mul]
  have d3 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iHᴴ * (pHᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, h3, conjTranspose_one, Matrix.one_mul]
  have d4 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iWᴴ * (pHᴴ * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, h4, conjTranspose_zero, Matrix.zero_mul]
  have e1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), sWᴴ * (GW * (sW * X)) = GW * X := fun X => by
    simp only [← Matrix.mul_assoc, hW.2.1]
  have e2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), sHᴴ * (GH * (sH * X)) = GH * X := fun X => by
    simp only [← Matrix.mul_assoc, hH.2.1]
  have f1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), sW * (sW * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hW.1, Matrix.one_mul]
  have f2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), sH * (sH * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hH.1, Matrix.one_mul]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, c1, c2, c3, c4, f1, f2, Matrix.mul_zero, add_zero,
      zero_add]
    simpa only [Matrix.mul_assoc] using hsum
  · rw [Matrix.mul_assoc, hGs]
    conv_rhs => rw [hG]
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, d1, d2, d3, d4,
      e1, e2, Matrix.mul_zero, add_zero, zero_add]
  · rw [hGs]
    have hPW := hW.2.2
    have hPH := hH.2.2
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      ((hPW.posSemidef.conjTranspose_mul_mul_same pW).add (hPH.posSemidef.conjTranspose_mul_mul_same pH)).1
      fun x hx => ?_
    have key : ∀ {n} (P : Matrix (Fin n) (Fin k) ℂ) (M : Matrix (Fin n) (Fin n) ℂ),
        star x ⬝ᵥ ((Pᴴ * M * P) *ᵥ x) = star (P *ᵥ x) ⬝ᵥ (M *ᵥ (P *ᵥ x)) := fun P M => by
      simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]
    rw [Matrix.add_mulVec, dotProduct_add, key, key]
    have hx' : iW *ᵥ (pW *ᵥ x) + iH *ᵥ (pH *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hsum, Matrix.one_mulVec]
    by_cases hw : pW *ᵥ x = 0
    · have hh : pH *ᵥ x ≠ 0 := fun hh => hx (by rw [← hx', hw, hh, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero])
      rw [hw]
      simpa using hPH.dotProduct_mulVec_pos hh
    · exact add_pos_of_pos_of_nonneg (hPW.dotProduct_mulVec_pos hw)
        (hPH.posSemidef.dotProduct_mulVec_nonneg _)


open Matrix in
theorem isCartanInv_sumMat : ∀ (D : D7) (B W H : HSp D) (o : OrthDec B W H) (sW : RealMat W) (sH : RealMat H), (∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → ∀ τ, IsCartanInv (gramAt D B τ) (sumMat o sW sH τ) := by
  intro D B W H o sW sH hW hH τ
  have hc : Function.Semiconj (tauE D τ) star star := fun x => GlobalTheory.FockCompare.tauE_star τ x
  have mm : ∀ {a b d : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) (N : Matrix (Fin b) (Fin d) D.host.E),
      (M * N).map (tauE D τ) = M.map (tauE D τ) * N.map (tauE D τ) := fun M N => Matrix.map_mul
  have ct : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), Mᴴ.map (tauE D τ) = (M.map (tauE D τ))ᴴ :=
    fun M => Matrix.conjTranspose_map _ hc
  have m1 : ∀ {a : ℕ}, (1 : Matrix (Fin a) (Fin a) D.host.E).map (tauE D τ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have m0 : ∀ {a b : ℕ}, (0 : Matrix (Fin a) (Fin b) D.host.E).map (tauE D τ) = 0 := Matrix.map_zero _ (map_zero _)
  rw [sumMat_apply]
  refine isCartanInv_blockSum (gramAt D B τ) (gramAt D W τ) (gramAt D H τ) (o.iA.map (tauE D τ))
    (o.iB.map (tauE D τ)) (o.qA.map (tauE D τ)) (o.qB.map (tauE D τ)) (sW τ) (sH τ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (hW τ) (hH τ)
  · show ((HSpace.gram B).map (tauE D τ))ᴴ = (HSpace.gram B).map (tauE D τ)
    rw [← ct, gram_conjTranspose]
  · show (o.iA.map (tauE D τ))ᴴ * (HSpace.gram B).map (tauE D τ) * o.iA.map (tauE D τ) = (HSpace.gram W).map (tauE D τ)
    rw [← ct, ← mm, ← mm, o.isoA]
  · show (o.iB.map (tauE D τ))ᴴ * (HSpace.gram B).map (tauE D τ) * o.iB.map (tauE D τ) = (HSpace.gram H).map (tauE D τ)
    rw [← ct, ← mm, ← mm, o.isoB]
  · show (o.iB.map (tauE D τ))ᴴ * (HSpace.gram B).map (tauE D τ) * o.iA.map (tauE D τ) = 0
    rw [← ct, ← mm, ← mm, o.orth, m0]
  · rw [← mm, o.qA_iA, m1]
  · rw [← mm, o.qA_iB, m0]
  · rw [← mm, o.qB_iB, m1]
  · rw [← mm, o.qB_iA, m0]
  · rw [← mm, ← mm, ← Matrix.map_add _ (map_add _), o.iA_qA_add, m1]

end GlobalTheory.Core.Rk.SumBox
end
end

section

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox
open scoped TensorProduct

namespace GlobalTheory.Core.Rk.SumBoxSph

variable {D : D7}

theorem rat_mul_gen {k l m : ℕ} (q : Matrix (Fin k) (Fin l) D.host.E) (p : AF D.host.F) (a : D.host.E)
    (t : Fin l → D.host.E) (z : Fin m → D.host.E) :
    rat q ⬝ (Matrix.of fun i j => (p ⊗ₜ[D.host.F] (a * t i * z j) : AE D) : Mx D l m) =
      (Matrix.of fun i j => (p ⊗ₜ[D.host.F] (a * (q *ᵥ t) i * z j) : AE D) : Mx D k m) := by
  ext i j
  have h : ∀ e y : D.host.E, incA D e * (p ⊗ₜ[D.host.F] y : AE D) = p ⊗ₜ[D.host.F] (e * y) := fun e y => by
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) * (p ⊗ₜ[D.host.F] y) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  show ∑ r, incA D (q i r) * (p ⊗ₜ[D.host.F] (a * t r * z j) : AE D) = p ⊗ₜ[D.host.F] (a * (∑ r, q i r * t r) * z j)
  rw [Finset.mul_sum, Finset.sum_mul, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [h]
  congr 1
  ring

theorem resT_mem_latO {A B W H : HSp D} (o : OrthDec B W H) {LA : Lat A} {LW : Lat W} {LH : Lat H}
    {P : FinPl D → Prop} {u : WO A B} (hu : u ∈ latO A B LA (sumLatO o LW LH) P) :
    o.resT A u ∈ (latO A W LA LW P).prod (latO A H LA LH P) := by
  have key : latO A B LA (sumLatO o LW LH) P ≤
      ((latO A W LA LW P).prod (latO A H LA LH P)).comap (o.resT A).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    obtain ⟨x, hx, x', hx', rfl⟩ := (mem_sumLatO o LW LH t).1 ht
    have e₁ : o.qA *ᵥ (o.iA *ᵥ x + o.iB *ᵥ x') = x := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.qA_iA, o.qA_iB, Matrix.one_mulVec,
        Matrix.zero_mulVec, add_zero]
    have e₂ : o.qB *ᵥ (o.iA *ᵥ x + o.iB *ᵥ x') = x' := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.qB_iA, o.qB_iB, Matrix.one_mulVec,
        Matrix.zero_mulVec, zero_add]
    refine ⟨AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, x, hx, ?_⟩,
      AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, x', hx', ?_⟩⟩
    · have := rat_mul_gen o.qA (pairA D.host.F 0 α) a (o.iA *ᵥ x + o.iB *ᵥ x') fun j => ∑ k, star (s k) * A.gram k j
      rw [e₁] at this
      exact this
    · have := rat_mul_gen o.qB (pairA D.host.F 0 α) a (o.iA *ᵥ x + o.iB *ᵥ x') fun j => ∑ k, star (s k) * A.gram k j
      rw [e₂] at this
      exact this
  exact key hu

theorem isHalf_mul {k l m : ℕ} {e : AE D} (p : Mx D k l) {u : Mx D l m} (hu : IsHalf e u) : IsHalf e (p ⬝ u) := by
  intro i j
  show e * ∑ r, p i r * u r j = ∑ r, p i r * u r j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by rw [mul_left_comm, hu r j]

theorem isSphOff_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B W H : HSp D) (o : OrthDec B W H) (LA : Lat A) (LW : Lat W) (LH : Lat H) (Sf : Finset (FinPl D)) (Φ : WO A W → ℂ) (Φ' : WO A H → ℂ), IsSphOff ψ A W LA LW Sf Φ → IsSphOff ψ A H LA LH Sf Φ' → IsSphOff ψ A B LA (sumLatO o LW LH) Sf (o.boxT A Φ Φ') := by
  intro D ψ A B W H o LA LW LH Sf Φ Φ' h₁ h₂
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · obtain ⟨hL, hR⟩ := resT_mem_latO o hu
    rw [o.heisO_boxT, map_nsmul, Prod.smul_fst, Prod.smul_snd, h₁.1 _ hL, h₂.1 _ hR]
  · obtain ⟨hL, hR⟩ := resT_mem_latO o hu
    rw [o.heisO_boxT, h₁.2 e he _ hL (isHalf_mul o.pA hh), h₂.2 e he _ hR (isHalf_mul o.pB hh)]

end GlobalTheory.Core.Rk.SumBoxSph

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
open GlobalTheory.Core.Rk.SumBox

noncomputable section

namespace GlobalTheory.Core.Rk.SumBox

variable {D : D7}

theorem pair_eq_dot (n : ℕ) (G : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_iA {B W H : HSp D} (o : OrthDec B W H) (x : Fin W.rank → D.host.E) (y : Fin B.rank → D.host.E) :
    ∑ i, ∑ j, star ((o.iA *ᵥ x) i) * B.gram i j * y j = ∑ i, ∑ j, star (x i) * W.gram i j * (o.qA *ᵥ y) j := by
  have hq : W.gram * o.qA = o.iAᴴ * B.gram := by
    rw [OrthDec.qA, Matrix.mul_nonsing_inv_cancel_left _ _ (gram_isUnit_det W)]
  rw [pair_eq_dot, pair_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hq]

theorem pair_iB {B W H : HSp D} (o : OrthDec B W H) (x : Fin H.rank → D.host.E) (y : Fin B.rank → D.host.E) :
    ∑ i, ∑ j, star ((o.iB *ᵥ x) i) * B.gram i j * y j = ∑ i, ∑ j, star (x i) * H.gram i j * (o.qB *ᵥ y) j :=
  pair_iA o.symm x y

theorem split_vec {B W H : HSp D} (o : OrthDec B W H) (y : Fin B.rank → D.host.E) :
    o.iA *ᵥ (o.qA *ᵥ y) + o.iB *ᵥ (o.qB *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.iA_qA_add, Matrix.one_mulVec]

theorem qA_split {B W H : HSp D} (o : OrthDec B W H) (x : Fin W.rank → D.host.E) (x' : Fin H.rank → D.host.E) :
    o.qA *ᵥ (o.iA *ᵥ x + o.iB *ᵥ x') = x := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.qA_iA, o.qA_iB, Matrix.one_mulVec,
    Matrix.zero_mulVec, add_zero]

theorem qB_split {B W H : HSp D} (o : OrthDec B W H) (x : Fin W.rank → D.host.E) (x' : Fin H.rank → D.host.E) :
    o.qB *ᵥ (o.iA *ᵥ x + o.iB *ᵥ x') = x' := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.qB_iA, o.qB_iB, Matrix.one_mulVec,
    Matrix.zero_mulVec, zero_add]

theorem iA_mem_sumLatO {B W H : HSp D} (o : OrthDec B W H) {LW : Lat W} (LH : Lat H) {x : Fin W.rank → D.host.E}
    (hx : x ∈ LW) : o.iA *ᵥ x ∈ sumLatO o LW LH :=
  (mem_sumLatO o LW LH _).2 ⟨x, hx, 0, zero_mem _, by rw [Matrix.mulVec_zero, add_zero]⟩

theorem iB_mem_sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) {LH : Lat H} {x : Fin H.rank → D.host.E}
    (hx : x ∈ LH) : o.iB *ᵥ x ∈ sumLatO o LW LH :=
  (mem_sumLatO o LW LH _).2 ⟨0, zero_mem _, x, hx, by rw [Matrix.mulVec_zero, zero_add]⟩

theorem isLattice_sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) (LH : Lat H)
    (hW : Submodule.IsLattice D.host.E LW) (hH : Submodule.IsLattice D.host.E LH) :
    Submodule.IsLattice D.host.E (sumLatO o LW LH) := by
  exact Submodule.IsLattice.of_fg D.host.E ((hW.fg.map _).sup (hH.fg.map _))

theorem selfDual_sumLatO : ∀ (D : D7) (B W H : HSp D) (o : OrthDec B W H) (LW : Lat W) (LH : Lat H),
    IsSelfDualC W LW → IsSelfDualC H LH → IsSelfDualC B (sumLatO o LW LH) := by
  intro D B W H o LW LH hW hH
  refine ⟨isLattice_sumLatO o LW LH hW.1 hH.1, fun y => ⟨fun hy x hx => ?_, fun hy => ?_⟩⟩
  · obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := (mem_sumLatO o LW LH y).1 hy
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := (mem_sumLatO o LW LH x).1 hx
    obtain ⟨b₁, hb₁⟩ := (hW.2 y₁).1 hy₁ x₁ hx₁
    obtain ⟨b₂, hb₂⟩ := (hH.2 y₂).1 hy₂ x₂ hx₂
    refine ⟨b₁ + b₂, ?_⟩
    have e : ∑ i, ∑ j, star ((o.iA *ᵥ x₁ + o.iB *ᵥ x₂) i) * B.gram i j * (o.iA *ᵥ y₁ + o.iB *ᵥ y₂) j =
        ∑ i, ∑ j, star ((o.iA *ᵥ x₁) i) * B.gram i j * (o.iA *ᵥ y₁ + o.iB *ᵥ y₂) j +
          ∑ i, ∑ j, star ((o.iB *ᵥ x₂) i) * B.gram i j * (o.iA *ᵥ y₁ + o.iB *ᵥ y₂) j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply, star_add]
      ring
    rw [e, pair_iA, pair_iB, qA_split, qB_split, ← hb₁, ← hb₂]
    push_cast
    ring
  · have hA : o.qA *ᵥ y ∈ LW := (hW.2 _).2 fun x hx => by
      obtain ⟨b, hb⟩ := hy _ (iA_mem_sumLatO o LH hx)
      exact ⟨b, hb.trans (pair_iA o x y)⟩
    have hB : o.qB *ᵥ y ∈ LH := (hH.2 _).2 fun x hx => by
      obtain ⟨b, hb⟩ := hy _ (iB_mem_sumLatO o LW hx)
      exact ⟨b, hb.trans (pair_iB o x y)⟩
    rw [← split_vec o y]
    exact (mem_sumLatO o LW LH _).2 ⟨_, hA, _, hB, rfl⟩

end GlobalTheory.Core.Rk.SumBox
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

variable {D : D7}

theorem isHalf_mul_right {e : AE D} {l m n : ℕ} {u : Mx D l m} (hu : IsHalf e u) (M : Mx D m n) : IsHalf e (u * M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [← mul_assoc, hu]

theorem isHalf_add_of {e : AE D} {m n : ℕ} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u + v) := by
  intro i j
  simp only [Matrix.add_apply, mul_add, hu i j, hv i j]

theorem isHalf_resS_iff {S A L T : HSp D} (o : OrthDec S A L) (e : AE D) (t : WO S T) :
    IsHalf e t ↔ IsHalf e (t * o.jA) ∧ IsHalf e (t * o.jB) := by
  refine ⟨fun h => ⟨isHalf_mul_right h _, isHalf_mul_right h _⟩, fun h => ?_⟩
  have ht : t = (o.resS T).symm (o.resS T t) := ((o.resS T).symm_apply_apply t).symm
  rw [ht, OrthDec.resS_symm_apply, OrthDec.resS_apply]
  exact isHalf_add_of (isHalf_mul_right h.1 _) (isHalf_mul_right h.2 _)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rd_sum_inl {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S A L T : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1))
    (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (t : WO S T) :
    (rd α₀ β t).submatrix id Sum.inl = rd α β (t * o.jA) := by
  have hs' : α₀.b = fromCols (o.jA.map p.pr * α.b) (replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) := hs
  simp only [rd, hs', Matrix.mul_fromCols]
  ext i j
  simp only [submatrix_apply, id, fromCols_apply_inl]
  rw [Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem rd_sum_inr {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S A L T : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1))
    (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (t : WO S T) :
    (fun i => rd α₀ β t i (Sum.inr 0)) = zcol β ζ (t * o.jB) := by
  have h1 : (t * o.jB) *ᵥ (fun j => incA D (ζ j)) = t *ᵥ ratV (vecB o ζ) := by
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext i
    exact (RingHom.map_mulVec (incA D) o.iB ζ i).symm
  have hs' : α₀.b = fromCols (o.jA.map p.pr * α.b) (replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) := hs
  funext i
  simp only [rd, hs', Matrix.mul_fromCols, fromCols_apply_inr, zcol, h1]
  rw [show (fun i => p.pr ((t *ᵥ ratV (vecB o ζ)) i)) = t.map p.pr *ᵥ fun i => p.pr (ratV (vecB o ζ) i) from
    funext fun i => RingHom.map_mulVec p.pr t _ i]
  rw [Matrix.mulVec_mulVec]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, replicateCol]

theorem extFun_tensCol_sum (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S A L T : HSp D)
    (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n) :
    IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ),
      extFun α₀ β (tensCol Ψ a) = o.boxS T (extFun α β Ψ) (GlobalTheory.FinPl.ExtZero.colFun β ζ a) := by
  intro hs Ψ a
  funext t
  simp only [extFun, OrthDec.boxS, colFun]
  have key : IsHalf p.e t ↔ IsHalf p.e (o.resS T t).1 ∧ IsHalf p.e (o.resS T t).2 := isHalf_resS_iff o p.e t
  by_cases h : IsHalf p.e t
  · obtain ⟨hA, hL⟩ := key.1 h
    rw [if_pos h, if_pos hA, if_pos hL, tensCol, rd_sum_inl o ζ α α₀ β hs, rd_sum_inr o ζ α α₀ β hs]
    rfl
  · rw [if_neg h]
    by_cases hA : IsHalf p.e (o.resS T t).1
    · rw [if_neg fun hL => h (key.2 ⟨hA, hL⟩), mul_zero]
    · rw [if_neg hA, zero_mul]

end GlobalTheory.FinPl.ExtZero
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw


theorem _root_.GlobalTheory.T.doublingSiegelLeviDetHom_levi_mul_unipotent : ∀ (D : D7) (A : HSp D) (p : siegel A) (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c → aP A p = Matrix.GeneralLinearGroup.det a := by
  first | exact @GlobalTheory.Core.Rk.SWLaw.aP_levi_mul_nC | exact GlobalTheory.Core.Rk.SWLaw.aP_levi_mul_nC | (intros; apply GlobalTheory.Core.Rk.SWLaw.aP_levi_mul_nC <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw


theorem _root_.GlobalTheory.T.doublingSiegel_eq_levi_mul_unipotent : ∀ (D : D7) (A : HSp D) (p : siegel A), ∃ (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c := by
  first | exact @GlobalTheory.Core.Rk.SWLaw.siegel_eq_levi_nC | exact GlobalTheory.Core.Rk.SWLaw.siegel_eq_levi_nC | (intros; apply GlobalTheory.Core.Rk.SWLaw.siegel_eq_levi_nC <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.wittLeviTransvection_mem_compactAtPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ (i j : Fin ρ) (hij : i ≠ j) (r : AE D), r ∈ idAt D (· = v) → (∀ a ∈ idAt D (· = v), colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v)) → InK S L (· = v) (d.levi (GlobalTheory.GLGen.transvGL hij r)) := by
  first | exact @GlobalTheory.FinPl.RootKeep.inK_levi_transv | exact GlobalTheory.FinPl.RootKeep.inK_levi_transv | (intros; apply GlobalTheory.FinPl.RootKeep.inK_levi_transv <;> assumption)
end
end
