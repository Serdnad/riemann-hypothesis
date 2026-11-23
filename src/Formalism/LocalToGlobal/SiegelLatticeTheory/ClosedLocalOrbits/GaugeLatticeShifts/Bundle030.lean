module

import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfLeviAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle028
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DualCoords
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LeviMul
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFrameWZeroExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LatSpanLeSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

namespace JL

def RightInvS : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ),
    FrameLoc ε k e z z' T T' →
    ∀ μ : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μ →
    ∀ s ∈ SLoc ε e z, μ.map (fun x => x * s) = μ

theorem frameLoc_swap {n r k : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T T' : ℝ}
    (hF : FrameLoc ε k e z z' T T') : FrameLoc ε k e z' z T' T :=
  ⟨hF.dim, hF.k_pos, hF.sig, hF.e_li, hF.ee, hF.ez', hF.ez, hF.zz', hF.zz, hF.T'_pos, hF.T_pos⟩

theorem lintegral_mul_right_of_map {n : ℕ} {ε : Fin n → Bool} (μ : Measure (Formalism.REAL.UJ ε))
    (t : Formalism.REAL.UJ ε) (hμ : μ.map (fun x => x * t) = μ) (F : Formalism.REAL.UJ ε → ℝ≥0∞) :
    ∫⁻ x, F (x * t) ∂μ = ∫⁻ x, F x ∂μ := by
  have hE : MeasurableEmbedding (fun x : Formalism.REAL.UJ ε => x * t) :=
    (MeasurableEquiv.mulRight t).measurableEmbedding
  calc ∫⁻ x, F (x * t) ∂μ = ∫⁻ x, F x ∂(μ.map (fun x => x * t)) := (hE.lintegral_map F).symm
    _ = ∫⁻ x, F x ∂μ := by rw [hμ]

theorem inner_dc {n : ℕ} {ε : Fin n → Bool} (μS μS' : Measure (Formalism.REAL.UJ ε))
    (s₁ s₁' g : Formalism.REAL.UJ ε) (h₁ : μS.map (fun x => x * s₁) = μS)
    (h₁' : μS'.map (fun x => x * s₁') = μS') (φ : Formalism.REAL.UJ ε → ℝ≥0∞) :
    ∫⁻ s, ∫⁻ s', φ (s * (s₁ * g * s₁'⁻¹) * s'⁻¹) ∂μS' ∂μS = ∫⁻ s, ∫⁻ s', φ (s * g * s'⁻¹) ∂μS' ∂μS := by
  have key : ∀ s s' : Formalism.REAL.UJ ε,
      φ (s * (s₁ * g * s₁'⁻¹) * s'⁻¹) = φ ((s * s₁) * g * (s' * s₁')⁻¹) := by
    intro s s'
    congr 1
    group
  have inner : ∀ x : Formalism.REAL.UJ ε,
      ∫⁻ s', φ (x * g * (s' * s₁')⁻¹) ∂μS' = ∫⁻ s', φ (x * g * s'⁻¹) ∂μS' := fun x =>
    lintegral_mul_right_of_map μS' s₁' h₁' (fun y => φ (x * g * y⁻¹))
  simp_rw [key, inner]
  exact lintegral_mul_right_of_map μS s₁ h₁ (fun x => ∫⁻ s', φ (x * g * s'⁻¹) ∂μS')

theorem measurableSet_goodLoc (r : ℕ) (T T' : ℝ) : MeasurableSet (GoodLoc (r := r) T T') := by
  apply Formalism.L2.SG.RealObj.InfCut.ProductExactness.measurableSet_goodLoc <;> assumption

end JL

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
end
end

section

namespace Formalism.L2.SG.Pf.SlabCount

theorem leviFinC_of_pos (hP : LeviPosC) : LeviFinC :=
  leviFinC_of (leviStabFinC_of (leviWFinC_of hP) rational_z_condition_holds)

theorem levi_finite_index : LeviFinC :=
  leviFinC_of_pos levi_totally_positive_definite

end Formalism.L2.SG.Pf.SlabCount
end

section

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.BridgeAd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hermitian_module_dual_beta_congruence {m : VA X.B.I} (hm : m ∈ Mo X.B.I X.B.g (Set.range X.e0)) (j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I m (X.bwd j)) := by
  rw [hA_symm]
  refine Z_sig X.B.I X.B.g (Z_pair_Mo X (X.vectorsInLattice.2.2 j).2 ?_ _ hm)
  rintro _ ⟨a, rfl⟩
  exact dual_beta_reference_congruence j a

theorem mem_module_of_congruences {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) v))
    (hz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 v)) (hbd : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd l) v))
    (hb : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bw l) v)) : v ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hd := dual_coords X hv
  rw [show v = (v - repr0 X v) + repr0 X v by abel]
  refine add_mem (mL_Mo X.B.I hd) ?_
  unfold repr0
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · refine sum_mem fun a _ => ?_
    have : hA X.B.I (X.f0 a) v • X.e0 a = (⟨_, hA_int X.B.I (hF a) hv⟩ : IntAf X.B.I.F X.B.I.E) • X.e0 a := rfl
    rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I ⟨a, rfl⟩)
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (he a) (hF a))
  · exact mL_Mo X.B.I (Z_smul_mL X hz hZ)
  · exact sum_mem fun l _ => mL_Mo X.B.I (Z_smul_mL X (hbd l) (hB l))
  · exact sum_mem fun l _ => mL_Mo X.B.I (Z_smul_mL X (hb l) (hBd l))

theorem hA_bwd_K (δ : X.B.I.Gf) (k j : Fin D.R.k) : hA X.B.I (X.bwd k) (X.B.I.fmat δ *ᵥ X.bwd j) = 0 := by
  rw [X.bwd_w k, X.bwd_w j, Matrix.mulVec_smul, hA_smul_left, hA_smul_right, sigA_sigA]
  have := X.ew_orth
  linear_combination (hA X.B.I (X.bwd k) (X.B.I.fmat δ *ᵥ X.bwd j)) * this

variable {X} (TR : TypedRed X)
include TR

theorem adTriv_inv {δ : X.B.I.Gf} (hK : δ ∈ X.B.I.Kset) (hN : NCong X δ) (hT : Formalism.L2.SG.Pf.AdTriv X δ) :
    Formalism.L2.SG.Pf.AdTriv X δ⁻¹ := by
  have gδ := good_of_ncong X hK hN
  have h1 : levi TR δ = 1 := (Formalism.L2.SG.Pf.IotaDictPf.levi_one_iff TR gδ).2 hT
  refine (Formalism.L2.SG.Pf.IotaDictPf.levi_one_iff TR (good_inv X gδ)).1 ?_
  rw [levi_inv TR gδ, h1, inv_one]

theorem adTriv_bwd {δ : X.B.I.Gf} (hK : δ ∈ X.B.I.Kset) (hN : NCong X δ) (hT : Formalism.L2.SG.Pf.AdTriv X δ) (j : Fin D.R.k) :
    (X.B.I.fmat δ - 1) *ᵥ X.bwd j ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hNi := ncong_inv X hK hN
  have hTi := adTriv_inv TR hK hN hT
  have hadj : ∀ y : VA X.B.I, hA X.B.I y ((X.B.I.fmat δ - 1) *ᵥ X.bwd j) =
      hA X.B.I ((X.B.I.fmat δ⁻¹ - 1) *ᵥ y) (X.bwd j) := by
    intro y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, hA_adj, Matrix.sub_mulVec, Matrix.one_mulVec,
      hA_sub_left]
  refine mem_module_of_congruences X (K_sub_mv X.B.I hK (hBd j)) (fun a => ?_) ?_ (fun l => ?_) (fun l => ?_)
  · rw [hadj]
    exact hermitian_module_dual_beta_congruence X (Mo_mono X.B.I (Set.image_subset_range _ _) (hNi.1 a)) j
  · rw [hadj]; exact hermitian_module_dual_beta_congruence X hNi.2 j
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, hA_bwd_K, hA_bwd_bwd, sub_zero]
    exact Z_zero X.B.I X.B.g
  · rw [hadj]; exact hermitian_module_dual_beta_congruence X (hTi l) j

theorem adFull_of_adTriv {δ : X.B.I.Gf} (hK : δ ∈ X.B.I.Kset) (hN : NCong X δ) (hT : Formalism.L2.SG.Pf.AdTriv X δ)
    {w : VA X.B.I} (hw : w ∈ X.B.I.Lf) (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) w)) :
    (X.B.I.fmat δ - 1) *ᵥ w ∈ Mo X.B.I X.B.g (Set.range X.e0) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hd := dual_coords X hw
  have hsm : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (m : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E →
      m ∈ Mo X.B.I X.B.g (Set.range X.e0) → c • m ∈ Mo X.B.I X.B.g (Set.range X.e0) := fun c m hc hm => by
    have : c • m = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • m := rfl
    rw [this]; exact Submodule.smul_mem _ _ hm
  rw [show w = (w - repr0 X w) + repr0 X w by abel, Matrix.mulVec_add]
  refine add_mem (mL_Mo X.B.I ?_) ?_
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (mem_mL_of_Kset X hK _ hd) hd
  unfold repr0
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, mulVec_fsum X, Matrix.mulVec_smul]
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact sum_mem fun a _ => hsm _ _ (hA_int X.B.I (hF a) hw)
      (Mo_mono X.B.I (Set.image_subset_range _ _) (hN.1 a))
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (he a) (K_sub_mv X.B.I hK (hF a)))
  · exact hsm _ _ (hA_int X.B.I hZ hw) hN.2
  · exact sum_mem fun l _ => hsm _ _ (hA_int X.B.I (hBd l) hw) (hT l)
  · exact sum_mem fun l _ => hsm _ _ (hA_int X.B.I (hB l) hw) (adTriv_bwd TR hK hN hT l)

end Formalism.L2.SG.Pf.BridgeAd
end
end

section

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IotaBridgeARC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ u →
    ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (b : X.B.I.GA), RatLink X b β →
      (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 * (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)
        ∈ X.B.I.Kset →
      NCong X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) →
      AdTriv X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) → RatTriv u X Λ β

def IotaBridgeRAC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ u →
    ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (b : X.B.I.GA), RatLink X b β →
      (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 * (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)
        ∈ X.B.I.Kset →
      NCong X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)) →
      RatTriv u X Λ β → AdTriv X ((((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ * b.2 *
        (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u))

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.RealObj.InfCut

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

def StepPtRepDiag : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ (i0 : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k), PtRepExists X u u' sc i0 i0

namespace PtRepPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hJ_crd (v : InfinitePlace X.B.I.F) (x y : (VS D).V) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd x)) (rv X.B.I v (X.crd y)) = X.B.I.φ v (X.ιE.symm ((VS D).hT x y)) := by
  rw [← Formalism.L2.SG.PoincareInHH.Cut.hform_crd (X := X) x y]
  first
  | rw [RingEquiv.symm_apply_apply]
  | simp only [RingEquiv.symm_apply_apply]
  | simp
  exact PI.ScPiFrameW.hJ_rv X.B.I v (X.crd x) (X.crd y)

def frU (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Fr (X.B.I.ε v) D.R.rS D.R.k where
  e := fun a => rv X.B.I v (X.eR a)
  fd := fun a => rv X.B.I v (X.fR a)
  z := rv X.B.I v (X.zR u)
  wb := X.wfr u v
  T := Tw u
  T_pos := by unfold Tw; exact_mod_cast (D.mem u).A.T_prime.pos
  card := by have h1 := X.n_eq; have h2 := Formalism.MainNotions.S.dimS_eq D.R; omega
  ee := fun a b => by
    show hJ _ (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd (X.eX b))) = 0
    rw [hJ_crd, X.ee, map_zero, map_zero]
  ff := fun a b => by
    show hJ _ (rv X.B.I v (X.crd (X.fY a))) (rv X.B.I v (X.crd (X.fY b))) = 0
    rw [hJ_crd, X.ff, map_zero, map_zero]
  ef := fun a b => by
    show hJ _ (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd (X.fY b))) = _
    rw [hJ_crd, X.ef]
    split_ifs <;> simp
  ez := fun a => by
    show hJ _ (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd (X.zu u))) = 0
    rw [hJ_crd, (X.zu_orth u a).1, map_zero, map_zero]
  fz := fun a => by
    show hJ _ (rv X.B.I v (X.crd (X.fY a))) (rv X.B.I v (X.crd (X.zu u))) = 0
    rw [hJ_crd, (X.zu_orth u a).2, map_zero, map_zero]
  zz := by
    show hJ _ (rv X.B.I v (X.crd (X.zu u))) (rv X.B.I v (X.crd (X.zu u))) = _
    rw [hJ_crd, X.zu_norm, map_neg, map_neg, map_natCast, map_natCast]
    simp [Tw]
  ww := X.wfr_on u v
  ew := fun a i => ((X.wfr_perp u v i).1 a).1
  fw := fun a i => ((X.wfr_perp u v i).1 a).2
  zw := fun i => (X.wfr_perp u v i).2

theorem zhatO_zhatO {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ZhatO (ZhatO Z) = Z := by
  ext a b
  simp only [Formalism.L2.SG.RealObj.ZhatO, ← mul_assoc, ← mul_pow]
  norm_num

theorem famSc_one {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : famSc 1 e z = fam e z := by
  funext a
  simp only [Formalism.L2.SG.RealObj.famSc, Complex.ofReal_one, one_pow, inv_one, one_smul]

end PtRepPf


open PtRepPf in
theorem real_point_representative_diagonal : StepPtRepDiag := by
  intro D X u u' sc hsc i0 w hw
  have hloc := fun v => locMain (frU X u v) (frU X u' v) rfl (i0 v) (ZhatO (ptC X v w)) (hw v) sc hsc
  choose g hgZ φ hφ hD using hloc
  have hω : ∀ v, hJ (X.B.I.ε v) (X.wfr u' v (i0 v)) (X.wfr u' v (i0 v)) = 1 := fun v => by
    rw [X.wfr_on, if_pos rfl]
  refine ⟨g, fun v => ?_, 1, fun v => rotU (X.B.I.ε v) (X.wfr u' v (i0 v)) (hω v) (φ v) (hφ v), ?_, ?_, ?_⟩
  · show ZhatO (Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat (g v))) = ptC X v w
    simp only [frm, famSc_one]
    rw [show Zhat (X.B.I.ε v) (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)))
        (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (uMat (g v)) = ZhatO (ptC X v w) from hgZ v,
      zhatO_zhatO]
  · intro v x _
    show uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) *ᵥ rv X.B.I v x = rv X.B.I v x
    simp [uMat]
  · intro v x hx
    rw [rotU_mulVec]
    have h0 : hJ (X.B.I.ε v) (X.wfr u' v (i0 v)) (rv X.B.I v x) = 0 := by
      rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
      · exact (frU X u' v).we (i0 v) a
      · exact (frU X u' v).wf (i0 v) a
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact (frU X u' v).wz (i0 v)
    rw [h0, mul_zero, zero_smul, add_zero]
  · intro v
    have hm1 : Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u v) v 1 = 1 := by
      ext a b
      show hJ (X.B.I.ε v) (X.wfr u v a) (uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) *ᵥ X.wfr u v b) = _
      simp [uMat, X.wfr_on, Matrix.one_apply]
    have hm2 : Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u' v) v
        (fun v => rotU (X.B.I.ε v) (X.wfr u' v (i0 v)) (hω v) (φ v) (hφ v)) =
        Matrix.diagonal fun i => if i = i0 v then φ v else 1 := by
      ext a b
      show hJ (X.B.I.ε v) (X.wfr u' v a)
        (uMat (rotU (X.B.I.ε v) (X.wfr u' v (i0 v)) (hω v) (φ v) (hφ v)) *ᵥ X.wfr u' v b) = _
      rw [rotU_mulVec, hJ_add_right, hJ_smul_right, X.wfr_on, X.wfr_on, X.wfr_on, diagonal_apply]
      by_cases hab : a = b
      · subst hab
        by_cases ha : a = i0 v
        · subst ha; simp
        · simp [ha, Ne.symm ha]
      · by_cases hb : b = i0 v
        · subst hb; simp [hab]
        · simp [hab, hb, Ne.symm hb]
    rw [hm1, hm2]
    exact hD v

theorem real_point_representative_exists : StepPtRep := real_point_representative_diagonal

end Formalism.L2.SG.RealObj.InfCut
end
end

section

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries

theorem haar_disintegration_of_local (h5 : JacobianCoordinates.P5) (hJ : JacobianCoordinates.JacLoc) (hS : JacobianCoordinates.SecMeasLoc) (hU : JacobianCoordinates.UnimodLoc)
    (hN : JacobianCoordinates.NHLoc) (hR : StepReal) : HaarDisintegrationReal :=
  h5 hJ DiagDCLoc_holds hS hU hN hR

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem frameLoc_X (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    FrameLoc (X.B.I.ε v) D.R.k (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u'))
      (Tw u) (Tw u') := by
  refine
    { dim := (Formalism.L2.SG.Pf.card_frame X).symm
      k_pos := by have := D.R.m_add_three_le_k; omega
      sig := Formalism.L2.SG.PoincareInHH.Cut.card_eps_false X v
      e_li := ?_
      ee := fun a b => (hJ_X X v _ _).trans (by rw [X.ee]; simp)
      ez := fun a => (hJ_X X v _ _).trans (by rw [(X.zu_orth u a).1]; simp)
      ez' := fun a => (hJ_X X v _ _).trans (by rw [(X.zu_orth u' a).1]; simp)
      zz := (hJ_X X v _ _).trans (by rw [X.zu_norm u]; simp [Tw])
      zz' := (hJ_X X v _ _).trans (by rw [X.zu_norm u']; simp [Tw])
      T_pos := Tw_pos u
      T'_pos := Tw_pos u' }
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.fR j))) hg
  rw [hJ_fsum_r] at h
  have hfe : ∀ i, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.eR i)) = if i = j then 1 else 0 :=
    fun i => (hJ_X X v _ _).trans (by rw [Formalism.L2.SG.PoincareInHH.Cut.hT_f_e X]; split_ifs <;> simp)
  simp only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [h]
  unfold hJ
  simp

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

section

namespace Formalism.L2.SG.Pf

theorem liftOntoC_of (hLI : ∀ D : Formalism.BasicNotions.D7, Formalism.L2.SG.TermTieOf.LatIso D) : Formalism.L2.SG.Pf.SatGram.LiftOntoC :=
  fun D X Y u u' => Act.liftOnto (hLI D) (ratPt_holds D X) Y u u' (toTermRel_holds X u u' _ _)

end Formalism.L2.SG.Pf
end
