module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNHomPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DualCoords
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FormHermitianPositive
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCoreGamProdSum
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCorePsiNatEquiv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsColLatRepS
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle020
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.Bundle001
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle012

@[expose] public section

section

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.CharacterOnFixedPoints

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem chiN_of_fix {κ : X.B.I.Gf} (h : ∀ a, (X.B.I.fmat κ - 1) *ᵥ nxt X.e0 X.z0 a ∈ mL X.B.I X.B.g) :
    chiN X κ = 1 := by
  unfold chiN
  refine psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (Formalism.L2.SG.Pf.ChiNHomPf.gB_ne_zero X) ?_
  refine Z_sum X.B.I X.B.g _ _ fun a _ => ?_
  have hf0 : X.f0 a ∈ X.B.I.Lf := (X.vectorsInLattice.1 a).2
  have e : X.B.I.fmat κ *ᵥ nxt X.e0 X.z0 a = nxt X.e0 X.z0 a + (X.B.I.fmat κ - 1) *ᵥ nxt X.e0 X.z0 a := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [e, hA_add_right]
  exact Z_add X.B.I X.B.g
    (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (Formalism.L2.SG.Pf.ChiNHomPf.hfe X) (Formalism.L2.SG.Pf.ChiNHomPf.hfz X) a)
    (mL_Qs X.B.I X.B.g hf0 (h a))

end Formalism.L2.SG.Pf.CharacterOnFixedPoints

namespace Formalism.L2.SG.NormCut

section KeyGen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

theorem key_gen (hTF : FrameTie X u u' F0 F0') (hM : Formalism.L2.SG.NormCut.ModGAt X)
    {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ ∈ what₂) (x : X.B.I.GA) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hRL : RatLink X x γ) (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (hξm : ∀ c, ModG (VS D) Λ (gS D) (γ (frame (lf D F0') c) - frameAct (frame (lf D F0)) ξ c))
    (hKp : kOf X u u' (cs.h (cs.base Λ) : X.B.I.Gf) (cs'.h (cs'.base Λ') : X.B.I.Gf) x ∈ X.B.I.Kset) :
    ∀ c, X.B.I.fmat (kOf X u u' (cs.h (cs.base Λ) : X.B.I.Gf) (cs'.h (cs'.base Λ') : X.B.I.Gf) x) *ᵥ
        (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c) -
      ∑ a, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a c : 𝓞 D.host.E) : D.host.E)) •
        (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 a) ∈ mL X.B.I X.B.g := by
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  set g1 : X.B.I.Gf := (cs.h (cs.base Λ) : X.B.I.Gf) * X.xu u with hg1
  set g2 : X.B.I.Gf := (cs'.h (cs'.base Λ') : X.B.I.Gf) * X.xu u' with hg2
  have hκK := hKp
  set κ := kOf X u u' (cs.h (cs.base Λ) : X.B.I.Gf) (cs'.h (cs'.base Λ') : X.B.I.Gf) x with hκ
  have hκ' : κ = g1⁻¹ * x.2 * g2 := rfl
  have hb : cs.lamOf (cs.base Λ) = Λ := cs.base_lam _ hΛ
  have hlat : ∀ y, y ∈ Λ ↔ X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf := fun y => by
    rw [← hb]; exact cs.lat_eq _ y

  set s : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
    fun a c => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a c : 𝓞 D.host.E) : D.host.E)) with hs
  have hsI : ∀ a c, s a c ∈ IntAf X.B.I.F X.B.I.E := fun a c => inclE_int X (ξ a c)

  set Y : Fin (D.R.rS + 1) → VA X.B.I := fun a => X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd (F0.fvec a)) with hY
  set Y' : Fin (D.R.rS + 1) → VA X.B.I := fun c => X.B.I.fmat g2⁻¹ *ᵥ incl X.B.I (X.crd (F0'.fvec c)) with hY'
  have key2 : ∀ c, InAt X.B.I X.B.g X.B.g (X.B.I.fmat κ *ᵥ Y' c - ∑ a, s a c • Y a) := by
    intro c
    have h1 := hM g1 Λ hlat _ (hξm c)
    have e : X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd (γ (frame (lf D F0') c) -
        frameAct (frame (lf D F0)) ξ c)) = X.B.I.fmat κ *ᵥ Y' c - ∑ a, s a c • Y a := by
      simp only [frameAct, crd_sub', crd_sum', crd_smul', incl_sub', incl_sum', incl_smul', Matrix.mulVec_sub,
        mulVec_fsum, Matrix.mulVec_smul, ratLink_incl X hRL]
      congr 1
      simp only [hY', Matrix.mulVec_mulVec, hκ', ← fmat_mul]
      congr 2
      group
    rw [e] at h1
    exact h1

  have fixE : ∀ (w : D.what₂.Word) (h : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w) (a : Fin D.R.rS),
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.eX a)) = incl X.B.I (X.crd (X.eX a)) :=
    fun w h a => fixes_inv X (fixes_mul X (h.2 _ (Or.inl (Or.inl ⟨a, rfl⟩))) ((X.xu_fix w a).1))
  have fixZ : ∀ (w : D.what₂.Word) (h : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w),
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) =
        X.B.I.fmat (X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) := by
    intro w h
    have hz : X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) = incl X.B.I (X.crd (X.zu w)) :=
      fixes_inv X (h.2 _ (Or.inr rfl))
    rw [_root_.mul_inv_rev, fmat_mul, ← Matrix.mulVec_mulVec, hz]
  set e0v : Fin (D.R.rS + 1) → VA X.B.I := Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 with he0v
  have hYa : ∀ a, InAt X.B.I X.B.g X.B.g (e0v a - Y a) := by
    intro a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [he0v, hY, Fin.snoc_last, FlagG.fvec, hTF.2.1, hg1, fixZ]
      have := InAt_neg X (X.xu_z u)
      rwa [neg_sub] at this
    · simp only [he0v, hY, Fin.snoc_castSucc, FlagG.fvec, hTF.1 i, hg1, fixE]
      exact (X.basisApprox i).1
  have hY'a : ∀ c, InAt X.B.I X.B.g X.B.g (e0v c - Y' c) := by
    intro c
    refine Fin.lastCases ?_ (fun i => ?_) c
    · simp only [he0v, hY', Fin.snoc_last, FlagG.fvec, hTF.2.2.2, hg2, fixZ]
      have := InAt_neg X (X.xu_z u')
      rwa [neg_sub] at this
    · simp only [he0v, hY', Fin.snoc_castSucc, FlagG.fvec, hTF.2.2.1 i, hg2, fixE]
      exact (X.basisApprox i).1
  have he0vL : ∀ a, e0v a ∈ X.B.I.Lf := fun a => by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [he0v, Fin.snoc_last]; exact hZ0
    · simp only [he0v, Fin.snoc_castSucc]; exact hE0 i
  have key4 : ∀ c, X.B.I.fmat κ *ᵥ e0v c - ∑ a, s a c • e0v a ∈ mL X.B.I X.B.g := by
    intro c
    have hsm : ∀ (z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (w : VA X.B.I), z ∈ IntAf X.B.I.F X.B.I.E → w ∈ X.B.I.Lf →
        z • w ∈ X.B.I.Lf := fun z w hz hw => by
      have : z • w = (⟨z, hz⟩ : IntAf X.B.I.F X.B.I.E) • w := rfl
      rw [this]; exact Submodule.smul_mem _ _ hw
    refine mem_mL_of_InAt X (sub_mem (K_mv X.B.I hκK (he0vL c)) (sum_mem fun a _ => hsm _ _ (hsI a c) (he0vL a))) ?_
    have e : X.B.I.fmat κ *ᵥ e0v c - ∑ a, s a c • e0v a =
        (X.B.I.fmat κ *ᵥ Y' c - ∑ a, s a c • Y a) + X.B.I.fmat κ *ᵥ (e0v c - Y' c) -
          ∑ a, s a c • (e0v a - Y a) := by
      simp only [Matrix.mulVec_sub, smul_sub, Finset.sum_sub_distrib]; abel
    rw [e]
    exact InAt_sub X (InAt_add X (key2 c) (InAt_K X hκK (hY'a c)))
      (InAt_sum X _ _ fun a _ => InAt_smul X (hsI a c) (hYa a))
  exact key4

end KeyGen

end Formalism.L2.SG.NormCut
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

set_option linter.dupNamespace false

namespace Formalism.L2.SG.RealObj.FlagExtensionRegularity

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.RealObj.HermitianBlockSpans Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fam_castLE {n r l : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (hl : l ≤ r) (h : l ≤ r + 1) (b : Fin l) :
    fam e z (Fin.castLE h b) = e (Fin.castLE hl b) := by
  have : Fin.castLE h b = Fin.castSucc (Fin.castLE hl b) := Fin.ext rfl
  rw [this, fam, Fin.snoc_castSucc]

theorem famSc_one {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : famSc 1 e z = fam e z := by
  funext a
  simp [famSc]

theorem span_map {n r : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (e : Fin r → Fin n → ℂ) (a : ℕ) {y : Fin n → ℂ}
    (hy : y ∈ spanLt e a) : g *ᵥ y ∈ spanLt (fun c => g *ᵥ e c) a := by
  unfold spanLt at *
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, hb, rfl⟩ := hw
    exact Submodule.subset_span ⟨b, hb, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add w1 w2 _ _ h1 h2 => rw [Matrix.mulVec_add]; exact add_mem h1 h2
  | smul c w _ h1 => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ h1

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem uMat_mul_inv' {n : ℕ} {ε : Fin n → Bool} (a : Formalism.REAL.UJ ε) : uMat a * uMat a⁻¹ = 1 := by
  simp [uMat]

theorem dl_eq (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) {l : ℕ} (hl : l ≤ D.R.rS) :
    Dl (ZX X u u' 1 γ v) l =
      (HermitianBlockSpans.blk (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => uMat (γ v) *ᵥ rv X.B.I v (X.eR a)) hl).det := by
  have h : l ≤ D.R.rS + 1 := hl.trans (Nat.le_succ _)
  unfold Dl
  rw [dite_eq_left h]
  congr 1
  ext b c
  simp only [Matrix.submatrix_apply, ZX, Zhat, frm, famSc_one, HermitianBlockSpans.blk, Matrix.of_apply]
  rw [fam_castLE _ _ hl h, fam_castLE _ _ hl h]

variable {X} {u u' : D.what₂.Word} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (X u u')

end Formalism.L2.SG.RealObj.FlagExtensionRegularity
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.SatGramActL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem satGramActLIota_kB_good {D : D7} {X : HidaSetting D} {w : D.what₂.Word}
    {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X w rs) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (γ : Gam X w) (hk : kB c Λ γ ∈ X.B.I.Kset) : Good X (kB c Λ γ) := by
  have e : kB c Λ γ = ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w)⁻¹ *
      (((iotaF X w γ * c.h (c.base Λ) : Hfin X w) : X.B.I.Gf) * X.xu w) := by
    simp only [kB, Subgroup.coe_mul, mul_assoc]
  rw [e] at hk ⊢
  refine colGood X w _ _ hk ?_
  have h2 := K_inv X.B.I hk
  rwa [mul_inv_rev, inv_inv] at h2

theorem levi_kB_mul_kBB_of_good {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) (γ : Gam X u) (hk : kB (Y.cs u) Λ γ ∈ X.B.I.Kset)
    (x : X.B.I.GA) (hG : Good X (kBB Y u u' Λ Λ' x)) :
    levi Y.TR (kB (Y.cs u) Λ γ * kBB Y u u' Λ Λ' x) = levi Y.TR (kB (Y.cs u) Λ γ) * levi Y.TR (kBB Y u u' Λ Λ' x) :=
  levi_mul Y.TR (satGramActLIota_kB_good (Y.cs u) Λ γ hk) hG

theorem iotaLeft_holds : IotaLeft := by
  intro D X Y u u' t γ hk
  exact levi_kB_mul_kBB_of_good Y u u' t.lam t.lam' γ hk t.rep.1.1
    (Formalism.L2.SG.Closed.AdmPar_holds (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') t)

end Formalism.L2.SG.Pf.SatGramActL
end
end

section

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.NormCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NormExpSatC' : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') →
    NormExpSat (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u')

def SatGramC' : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    SatGram (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (Y.tO u u').genSet
        (Aset Y.TR (Y.cs u)) (Aset Y.TR (Y.cs u')) ∧
      SatGram (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (Y.tO u u').ngSet
        (Aset Y.TR (Y.cs u)) (Aset Y.TR (Y.cs u'))

def ChiNBiC : Prop := ∀ (D : D7) (X : HidaSetting D), ChiNBi X

def NeatC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK

def LeviOntoC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.Pf.NormSteps.LeviOntoS Y.TR (Y.cs u)

theorem colLatRepC (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) :
    Formalism.L2.SG.Pf.NormSteps.ColLatRepS (Y.cs u) Y.hK :=
  Formalism.L2.SG.Pf.NormSteps.column_lattice_representatives (Y.cs u) Y.hK (Y.rowsOK u)

def MassAC : Prop := ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), MassA Y.TR (X.Fu u) (Y.cs u)

theorem normExpSatC'_of (hCL : NeatC) (hO : LeviOntoC) (hM : MassAC) (hS : SatGramC') : NormExpSatC' := by
  intro D X Y u u' _ _ _ hAbs
  obtain ⟨hSg, hSn⟩ := hS D X Y u u' ‹_› ‹_› ‹_›
  have hTF := Full.frameTie (X := X) u u'
  have hF := colFree_steps (TR := Y.TR) (F0 := X.Fu u) (cs := Y.cs u) (hK := Y.hK) (hR := Y.colReps u)
    (hCL := hCL D X Y u) (hO := hO D X Y u) (hRep := colLatRepC D X Y u) (hMass := hM D X Y u)
  have hF' := colFree_steps (TR := Y.TR) (F0 := X.Fu u') (cs := Y.cs u') (hK := Y.hK) (hR := Y.colReps u')
    (hCL := hCL D X Y u') (hO := hO D X Y u') (hRep := colLatRepC D X Y u') (hMass := hM D X Y u')
  exact normExpSat_of (TR := Y.TR) (cs := Y.cs u) (cs' := Y.cs u') (FdN := Y.FN u) (FdN' := Y.FN u')
    (hHS := hilbert_schmidt_blocks) (hGam := Formalism.L2.SG.NormCut.gamma_product_sum_holds)
    (hPsi := Formalism.L2.SG.NormCut.psi_natural_equiv_holds) (hAbs := hAbs)
    (hChi := chiNIndep_of_frameTie (cs := Y.cs u) (cs' := Y.cs u') (hTF := hTF))
    (sc := scOf Y.TR (Y.cs u)) (sc' := scOf Y.TR (Y.cs u'))
    (hPh := colPhase_holds (TR := Y.TR) (cs := Y.cs u) (cs' := Y.cs u') (hTF := hTF))
    (A := Aset Y.TR (Y.cs u)) (A' := Aset Y.TR (Y.cs u')) (hF := hF) (hF' := hF') (hSg := hSg) (hSn := hSn)

end Formalism.L2.SG.NormCut
end
end

section

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

namespace StabFlagPf

open Matrix

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def toVHom : (Fin X.B.I.n → X.B.I.E) →+ (VS D).V where
  toFun := Formalism.L2.SG.Pf.Level.toV X
  map_zero' := by simp [Formalism.L2.SG.Pf.Level.toV]
  map_add' := Formalism.L2.SG.Pf.Level.toV_add X

theorem toV_span {T : Set (Fin X.B.I.n → X.B.I.E)} {w : Fin X.B.I.n → X.B.I.E}
    (hw : w ∈ Submodule.span X.B.I.E T) :
    Formalism.L2.SG.Pf.Level.toV X w ∈ Submodule.span D.host.E (Formalism.L2.SG.Pf.Level.toV X '' T) :=
  Formalism.L2.SG.Pf.Vanish2.tr_span X.ιE.toRingHom (toVHom X) (fun c x => Formalism.L2.SG.Pf.Level.toV_smul X c x) hw

theorem flag_e {u' : D.what₂.Word} {s : X.B.I.GA} {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hs : RatLink X s σ) (hS : s ∈ Srat X u') (a : Fin D.R.rS) :
    σ (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {b | b.1 < a.1}) := by
  obtain ⟨M, -, -, h2, h3⟩ := hs
  obtain ⟨-, hsf⟩ := Formalism.L2.SG.PoincareInHH.Cut.sratComp_holds X u' _ hS
  obtain ⟨hfe, -⟩ := hsf
  have hf := hfe a
  have hG : ∀ y, X.B.I.fmat s.2 *ᵥ Formalism.L2.SG.Pf.Vanish2.inclHom X.B.I y =
      Formalism.L2.SG.Pf.Vanish2.inclHom X.B.I ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) := by
    intro y
    rw [Formalism.L2.SG.Pf.Vanish2.inclHom_apply, Formalism.L2.SG.Pf.Vanish2.inclHom_apply, h2]
    exact Formalism.L2.SG.Pf.Level.incl_mulVec X _ y
  have e := Formalism.L2.SG.Pf.Vanish2.tr_sub (Formalism.L2.SG.Pf.Vanish2.inclHom X.B.I) _ _ hG (X.eR a)
  rw [Formalism.L2.SG.Pf.Vanish2.inclHom_apply, Formalism.L2.SG.Pf.Vanish2.inclHom_apply] at e
  rw [e] at hf
  have hd := Formalism.L2.SG.Pf.Level.descend X _ _ hf
  have hm : ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) - 1) *ᵥ X.eR a = X.crd (σ (X.eX a) - X.eX a) :=
    Formalism.L2.SG.Pf.Vanish2.mcrd X h3 (X.eX a)
  rw [hm] at hd
  have ht := toV_span X hd
  rw [Formalism.L2.SG.Pf.Level.toV_crd, Set.image_image] at ht
  have e2 : (fun b => Formalism.L2.SG.Pf.Level.toV X (X.eR b)) = X.eX :=
    funext fun b => Formalism.L2.SG.Pf.Level.toV_crd X (X.eX b)
  rwa [e2] at ht

end StabFlagPf

theorem flag_stabilizer_holds : StabFlagC := by
  intro D X Y u u' _ s σ hs _ hS j x hx
  have e : ∀ k, Xflag (lf D (X.Fu u')) k = Submodule.span D.host.E (X.eX '' {i | i.1 < k}) := by
    intro k
    show Submodule.span D.host.E ((X.Fu u').e '' {i | i.1 < k}) = _
    rw [X.Fu_e]
  rw [e] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    refine Submodule.span_mono ?_ (StabFlagPf.flag_e X hs hS a)
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, lt_of_lt_of_le hb (Nat.lt_succ_iff.1 ha), rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add (f := _), add_sub_add_comm]
    exact add_mem hy hz
  | smul c y _ hy =>
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ _ hy

end Formalism.L2.SG.Pf.RegroupPf
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
open Formalism.L2.SG.HidaSetting Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

theorem rational_isomorphism_holds : RatIsoC := by
  intro D X γ hγ
  obtain ⟨g, hgU, h1, h2⟩ := PI.UnitaryGroupMassFormula.LCG.mem_gf X.B.I ⟨γ, hγ⟩
  let φ := (X.ιE : X.B.I.E →+* D.host.E).mapMatrix (m := Fin X.B.I.n)
  let Mg := φ (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  let Mi := φ ((g⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  have hmul1 : Mg * Mi = 1 := by
    simp only [Mg, Mi]
    rw [← map_mul, Units.mul_inv, map_one]
  have hmul2 : Mi * Mg = 1 := by
    simp only [Mg, Mi]
    rw [← map_mul, Units.inv_mul, map_one]
  let σ : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
    LinearEquiv.ofLinear (Matrix.toLin X.bas X.bas Mg) (Matrix.toLin X.bas X.bas Mi)
      (by rw [← Matrix.toLin_mul, hmul1, Matrix.toLin_one])
      (by rw [← Matrix.toLin_mul, hmul2, Matrix.toLin_one])
  have hcrd : ∀ y, X.crd (σ y) = (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := by
    intro y
    funext i
    show X.ιE.symm (X.bas.repr (Matrix.toLin X.bas X.bas Mg y) i) = _
    rw [Matrix.toLin_apply, Module.Basis.repr_sum_self]

    simp [Mg, φ, Matrix.mulVec, dotProduct, Formalism.L2.SG.HidaSetting.HidaSetting.crd,
    Formalism.L2.SG.HidaSetting.crdOf, map_sum, map_mul]
  refine ⟨σ, ⟨g, hgU, h1, h2, hcrd⟩, fun x y => ?_⟩
  rw [← Formalism.L2.SG.PoincareInHH.Cut.hform_crd (X := X) (σ x) (σ y),
    ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd (X := X) x y, hcrd, hcrd,
    Formalism.L2.SG.PoincareInHH.Cut.hform_mulVec _ _ _ hgU]

end Formalism.L2.SG.Pf.RegroupPf
end
end
