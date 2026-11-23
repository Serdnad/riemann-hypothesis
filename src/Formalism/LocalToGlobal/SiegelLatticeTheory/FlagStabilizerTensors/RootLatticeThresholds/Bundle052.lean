module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgePlace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle016
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsEtOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFwdPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle033
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.Bundle002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.BesselFunctionBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.Bundle001
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.IntegrableGNRpowOfLintegralLtTop
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.FlipOneThree
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.RStabInv
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

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.LocWSOf Formalism.MainNotions.S

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem n_eq : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have h := (PtRepPf.frU X (Classical.arbitrary D.what₂.Word) v).card
  omega

theorem trG_mul_inv (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) γ * trG (C.Q τ) (C.Qi τ) γ⁻¹ = 1 := by
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  unfold trG
  calc C.Qi τ * uMat γ * C.Q τ * (C.Qi τ * uMat γ⁻¹ * C.Q τ)
      = C.Qi τ * uMat γ * (C.Q τ * C.Qi τ) * uMat γ⁻¹ * C.Q τ := by simp only [Matrix.mul_assoc]
    _ = C.Qi τ * (uMat γ * uMat γ⁻¹) * C.Q τ := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul_inv, Matrix.mul_one, h1]

theorem trG_inv (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (trG (C.Q τ) (C.Qi τ) γ)⁻¹ = trG (C.Q τ) (C.Qi τ) γ⁻¹ :=
  Matrix.inv_eq_right_inv (trG_mul_inv C τ γ)

theorem trG_mul (τ : D.what₂.Tau) (a b : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) (a * b) = trG (C.Q τ) (C.Qi τ) a * trG (C.Q τ) (C.Qi τ) b := by
  obtain ⟨-, h2, -, -⟩ := C.isT τ
  unfold trG
  rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
  calc C.Qi τ * (uMat a * uMat b) * C.Q τ = C.Qi τ * uMat a * (C.Q τ * C.Qi τ) * uMat b * C.Q τ := by
        rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem haarTr_holds (u u' : D.what₂.Word) (τ : D.what₂.Tau) : HaarTr C u u' τ := by
  intro γ μRv hH
  obtain ⟨hσ, hne, hconc, hinv⟩ := hH
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  have hT := trHyp_C C u τ
  have hT' := trHyp_C C u' τ
  set f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun x => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x) with hf
  have hemb : Topology.IsClosedEmbedding f := Formalism.L2.SG.Pf.WuBL.trG_closedEmb' n_eq _ h2
  have hme : MeasurableEmbedding f := hemb.measurableEmbedding
  have hU : ∀ y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat y =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := fun y => y.2

  have hfwd : ∀ y ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ))
      (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ, trG (C.Q τ) (C.Qi τ) y ∈ RStab D.R.k D.R.rS (gB C τ γ) := by
    rintro y ⟨hy1, hy2⟩
    refine ⟨Formalism.L2.SG.Pf.Bridge.fwd_N hT (hU y) hy1, ?_⟩
    show (trG (C.Q τ) (C.Qi τ) γ)⁻¹ * trG (C.Q τ) (C.Qi τ) y * trG (C.Q τ) (C.Qi τ) γ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS
    rw [trG_inv, ← trG_mul, ← trG_mul]
    exact Formalism.L2.SG.Pf.Bridge.fwd_N hT' (hU _) hy2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hσ
    exact hme.sigmaFinite_map
  · intro h0
    apply hne
    have h := congrArg (fun m : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) => m Set.univ) h0
    simp only [FunLike.coe_zero, Pi.zero_apply] at h
    rw [hme.map_apply, Set.preimage_univ] at h
    exact Measure.measure_univ_eq_zero.1 h
  · rw [hme.map_apply]
    refine measure_mono_null (fun y hy => ?_) hconc
    intro hyS
    exact hy (hfwd y hyS)
  · intro s hs
    obtain ⟨hsN, hsN'⟩ := hs
    have hmem := Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hsN.1
    set y0 := Formalism.L2.SG.Pf.LocJEq.ujOf' (C.Q τ * s * C.Qi τ) hmem with hy0
    have hy0S : y0 ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ))
        (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ := by
      refine ⟨Formalism.L2.SG.Pf.Bridge.inN_Q hT hsN, ?_⟩
      show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat (γ⁻¹ * y0 * γ))
      have e : uMat (γ⁻¹ * y0 * γ) = C.Q τ * ((gB C τ γ)⁻¹ * s * gB C τ γ) * C.Qi τ := by
        rw [trG_inv]
        show uMat (γ⁻¹ * y0 * γ) = C.Q τ * (C.Qi τ * uMat γ⁻¹ * C.Q τ * s * (C.Qi τ * uMat γ * C.Q τ)) * C.Qi τ
        rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul, Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
        show uMat γ⁻¹ * (C.Q τ * s * C.Qi τ) * uMat γ = _
        simp only [← Matrix.mul_assoc]
        rw [h2, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
        rw [h2, Matrix.mul_one]
      rw [e]
      exact Formalism.L2.SG.Pf.Bridge.inN_Q hT' hsN'
    have hcomp : (Formalism.QuantumDeterminants.lmulM s) ∘ f = f ∘ (fun x => y0 * x) := by
      funext x
      simp only [Function.comp, hf, Formalism.QuantumDeterminants.lmulM]
      rw [trG_mul]
      congr 1
      show s = C.Qi τ * (C.Q τ * s * C.Qi τ) * C.Q τ
      simp only [← Matrix.mul_assoc]
      rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
    have hcont_l : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
      have : Continuous (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id
      exact this.measurable
    rw [Measure.map_map hcont_l hme.measurable, hcomp,
      ← Measure.map_map hme.measurable (continuous_const_mul y0).measurable, hinv y0 hy0S]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsClosed

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

theorem rhoSurj_X : Function.Surjective (AllRowsRhoX.rhoX X) := Formalism.L2.SG.Pf.RhoSurjW.reduction_map_surjective D X

theorem redKerOne_holds : RedKerOne X := redKerOne_of (X := X) (AllRowsRedKer.redKerP_holds X 0) (AllRowsRedKer.redKerP_holds X 1)

theorem etUniv_holds : EtUniv X := etUniv_of (X := X) (redKer_of (X := X) (redKerOne_holds X))

theorem etUnip_holds (k : Fin 2) (S : Set (Tup D k)) : EtUnip X k S := etUnip_of (X := X) k (AllRowsRedKer.redKerP_holds X (1 - k)) S

theorem kppShape_holds : AllRowsKpp.KppShape X := Formalism.L2.SG.Pf.AllRowsKpp.kppShape_of_fwd (X := X) (rhoSurj_X X) (Formalism.L2.SG.Pf.KppFwdPf.kppFwd_holds (X := X))

theorem etAlg_holds (S : Set (Tup2 D)) : EtAlg X S := Formalism.L2.SG.Pf.AllRowsEtAlg.etAlg_of (X := X) (rhoSurj_X X) S

theorem etOne_holds (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hψ₀ : ∀ k, ψ₀ k ≠ 1) : EtOne X ψ₀ := Formalism.L2.SG.Pf.AllRowsEtOne.etOne_of (X := X) (rhoSurj_X X) (kppShape_holds X) ψ₀ hψ₀

def allRowsOfL (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hψ₀ : ∀ k, ψ₀ k ≠ 1) (hL : RowsLab X) : AllRows D :=
  allRowsOfP X ψ₀ (AllRowsRedKer.redKerP_holds X 0) (AllRowsRedKer.redKerP_holds X 1) (etOne_holds X ψ₀ hψ₀) hL

end Formalism.L2.SG.Pf.AllRowsClosed
end
end

section

noncomputable section

namespace Formalism.L2.SG.AmpOrbClosed

open Formalism.BasicNotions Formalism.MainNotions.S



theorem ampDD_thm : Formalism.MainNotions.S.Pv.AmpDD.AmpDD :=
  Formalism.MainNotions.S.Pv.AmpDDPf.amplitude_orbital_integral Formalism.FourierDecayAlt.P.schur_hermitian Formalism.FourierDecayAlt.P.norm_inverse_bound
    Formalism.FourierDecayAlt.P.growth_group_bound Formalism.FourierDecayAlt.P.double_coset_decomposition Formalism.MainNotions.S.Pv.AmpDDPf.right_stabilizer_invariance



end Formalism.L2.SG.AmpOrbClosed
end
end
