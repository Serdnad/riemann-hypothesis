module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.Pf.WuDec

section Core

variable {k r : ℕ}

theorem lowSmoothSK {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {w : H}
    (hds : IsDSHpk k r ε lam σ) (hlow : IsLowUnitH k r ε lam σ w) : w ∈ smoothVecs (k := k) (r := r) σ :=
  Formalism.L2.SG.Pf.k_finite_smooth k r ε lam H σ hds w (PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow)

theorem besselUniq_core (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : Formalism.L2.SG.LitS.BesselMultOne)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {lam : Fin (2 * r + k + 1) → ℝ}
    {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat k r → (H →L[ℂ] H)}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hds : IsDSHpk k r ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hc : c ≠ 0)
    {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
    (hπ : IsHCTypeW k r z u π) {w : H} (hw : IsLowUnitH k r ε lam σ w) (hws : w ∈ smoothVecs (k := k) (r := r) σ)
    {μG μW μN ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hG : IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG) (hW : IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (hQ : IsQuotMeas μG (Formalism.MainNotions.S.muS μW μN) ν)
    {W W0 : Mat k r → Vp}
    (hc1 : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))) (he1 : IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W)
    (hr1 : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W x = W x)
    (hl1 : l2SG ν W ≠ 0) (hl1' : l2SG ν W < ⊤)
    (hc2 : ContinuousOn W0 (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))) (he2 : IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W0)
    (hr2 : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W0 (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W0 x = W0 x)
    (hl2 : l2SG ν W0 ≠ 0) (hl2' : l2SG ν W0 < ⊤)
    (hx0 : ∃ x0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W0 x0 ≠ 0) :
    ∃ a : ℂ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W x = a • W0 x := by
  obtain ⟨B, hB, hWB⟩ := hBW k r z c u lam ε h H σ hl hds hg hok hz hT hc Vp π hπ w hw μG μW μN ν hG hW hN hQ
    W hc1 he1 hr1 hl1 hl1'
  obtain ⟨B0, hB0, hW0B⟩ := hBW k r z c u lam ε h H σ hl hds hg hok hz hT hc Vp π hπ w hw μG μW μN ν hG hW hN hQ
    W0 hc2 he2 hr2 hl2 hl2'
  rw [Formalism.L2.SG.LitS.psi_eq_psiGen] at hB hB0
  obtain ⟨a, b, hab, hlin⟩ := hM1 k r ε lam H σ z (fun _ => c) u Vp π hl hds hz hT (fun _ => hc) hπ B B0 hB hB0
  have hsm : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ x w ∈ smoothVecs (k := k) (r := r) σ :=
    fun x hx => Formalism.L2.SG.BesselSplit.smooth_translate_ds hds hws hx
  by_cases ha : a = 0
  · exfalso
    have hb : b ≠ 0 := hab.resolve_left (not_not.2 ha)
    obtain ⟨x0, hx0U, hx0W⟩ := hx0
    have h1 := hlin (σ x0 w) (hsm x0 hx0U)
    rw [ha, zero_smul, zero_add] at h1
    have h2 : B0 (σ x0 w) = 0 := (smul_eq_zero.1 h1).resolve_left hb
    exact hx0W (by rw [hW0B x0 hx0U, h2])
  · refine ⟨-(b / a), fun x hx => ?_⟩
    have h1 := hlin (σ x w) (hsm x hx)
    rw [hWB x hx, hW0B x hx]
    have : a • B (σ x w) = -(b • B0 (σ x w)) := eq_neg_of_add_eq_zero_left h1
    calc B (σ x w) = a⁻¹ • (a • B (σ x w)) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      _ = -(b / a) • B0 (σ x w) := by
          rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

end Core

end Formalism.L2.SG.Pf.WuDec
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.DataInst

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7}

variable (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

def VIndepAt (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h₁ h₁' h₂ h₂', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h₁ h₁' →
      IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h₂ h₂' →
      (X.piU u h₁⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w)).comp
          (X.piU u' h₁')) =
        (X.piU u h₂⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w)).comp
          (X.piU u' h₂'))

end Formalism.L2.SG.Pf.Carrier
end
end

section

noncomputable section

open scoped Classical
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.LTL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lemmas

open scoped ComplexConjugate

theorem hsNormSq_nonneg {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  first
  | exact inner_self_nonneg (𝕜 := ℂ) (x := A (stdOrthonormalBasis ℂ Wq i))
  | (rw [inner_self_eq_norm_sq_to_K]; norm_cast; positivity)

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (c • A) = Complex.normSq c * hsNormSq A := by
  unfold hsNormSq hsInner
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, ← mul_assoc]
  rw [← Finset.mul_sum]
  first
  | rw [Complex.mul_conj]
  | rw [← Complex.normSq_eq_conj_mul_self]
  rw [Complex.re_ofReal_mul]

theorem isQuotMeas_smul {k r : ℕ} {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (h : IsQuotMeas μG μS ν) {c : ENNReal}
    (h0 : c ≠ 0) (hT : c ≠ ⊤) : IsQuotMeas μG (c • μS) (c⁻¹ • ν) := by
  intro f hf
  rw [h f hf]
  simp only [MeasureTheory.lintegral_smul_measure, smul_eq_mul]
  rw [MeasureTheory.lintegral_const_mul' c _ hT, ← mul_assoc, ENNReal.inv_mul_cancel h0 hT, one_mul]

theorem locJ_smul {k r : ℕ} {W : LocW k r} (A : LocS W) (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (c : ENNReal)
    (γ : MatKR k r) : A.J (c • ν) γ = ((c.toReal : ℝ) : ℂ) • A.J ν γ := by
  simp only [Formalism.MainNotions.S.LocS.J, Formalism.MainNotions.S.ampJ, MeasureTheory.integral_smul_measure]
  rw [Complex.coe_smul]
  exact smul_comm _ _ _

end Lemmas

section Tr

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem star_dot_conjT {n m : Type*} [Fintype n] [Fintype m] (Q : Matrix n m ℂ) (x : m → ℂ) (y : n → ℂ) :
    star x ⬝ᵥ (Qᴴ *ᵥ y) = star (Q *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem hJ_smul_real {n : ℕ} (ε : Fin n → Bool) (r s : ℝ) (x y : Fin n → ℂ) :
    hJ ε ((r : ℂ) • x) ((s : ℂ) • y) = ((r * s : ℝ) : ℂ) * hJ ε x y := by
  simp only [hJ]
  simp [Matrix.mulVec_smul, smul_eq_mul]
  try push_cast
  try ring

theorem frS_pow (D : D7) (a : Fin (D.R.rS + 1)) (h : a.val < D.R.rS) :
    frS D ^ (D.R.rS - a.val) = ((rhoF D a : ℝ) : ℂ) := by
  have hk : D.host.ka / (2 * Real.pi) = D.host.rdE⁻¹ := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    have hpi := Real.pi_pos.ne'
    rcases eq_or_ne D.host.rdE 0 with h0 | h0
    · rw [h0]
      simp
    · field_simp
      try ring
  have hnn : 0 ≤ D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_nonneg (abs_nonneg _) _
  have hc : ((D.R.rS - a.val : ℕ) : ℝ) = (D.R.rS : ℝ) - (a.val : ℝ) := by
    rw [Nat.cast_sub h.le]
  unfold frS rhoF
  rw [hk, ← hc, Real.rpow_neg hnn, Real.rpow_natCast, ← inv_pow]
  push_cast
  try ring

theorem rhoF_last (D : D7) : rhoF D (Fin.last D.R.rS) = 1 := by
  simp [rhoF, Fin.val_last]

theorem Q_fvec (u : D.what₂.Word) (τ : D.what₂.Tau) (a : Fin (D.R.rS + 1)) :
    C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a =
      ((rhoF D a : ℝ) : ℂ) • rv X.B.I (vOf X τ) (X.crd ((X.Fu u).fvec a)) := by
  obtain ⟨_, hQQi, _, hEv⟩ := C.isT τ
  by_cases h : a.val < D.R.rS
  · have h1 := (hEv ⟨a.val, h⟩ ⟨a.val, h⟩ rfl).1
    have ha : a = Fin.castSucc ⟨a.val, h⟩ := Fin.ext rfl
    have h2 : (X.Fu u).fvec (Fin.castSucc ⟨a.val, h⟩) = X.eX ⟨a.val, h⟩ := by
      simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
      exact congrFun (X.Fu_e u) _
    rw [← ha] at h2
    rw [h2, ← frS_pow D a h, Formalism.QuantumDeterminants.fvec, dite_eq_left h, Formalism.QuantumDeterminants.bvec, h1]
    rfl
  · have ha : a = Fin.last D.R.rS := Fin.ext (by have := a.isLt; simp; omega)
    subst ha
    have h3 : (X.Fu u).fvec (Fin.last D.R.rS) = X.zu u := by
      simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
      exact X.flagZVector u
    rw [h3, rhoF_last, Formalism.QuantumDeterminants.fvec, dite_eq_right h]
    simp only [zB, Complex.ofReal_one, one_smul]
    rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    rfl

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau := by
  exact D.eTau.nonempty

theorem trG_mem {n m : ℕ} {ε : Fin n → Bool} (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (H : Matrix (Fin m) (Fin m) ℂ) (hQQi : Q * Qi = 1) (hH : Qᴴ * Formalism.REAL.Jm ε * Q = H) (g : Formalism.REAL.UJ ε) :
    Formalism.L2.SG.RealObj.trG Q Qi g ∈ Formalism.QuantumDeterminants.UH H := by
  have hU : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := by
    first
    | exact g.2
    | (unfold uMat; exact g.2)
    | simpa [uMat] using g.2
  have h1 : ∀ X : Matrix (Fin n) (Fin m) ℂ, Qiᴴ * (Qᴴ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hQQi, Matrix.conjTranspose_one, Matrix.one_mul]
  have h2 : ∀ X : Matrix (Fin n) (Fin m) ℂ, Q * (Qi * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hQQi, Matrix.one_mul]
  have h3 : ∀ X : Matrix (Fin n) (Fin m) ℂ,
      (uMat g)ᴴ * (Formalism.REAL.Jm ε * (uMat g * X)) = Formalism.REAL.Jm ε * X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]
  show (Qi * uMat g * Q)ᴴ * H * (Qi * uMat g * Q) = H
  rw [← hH]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, h1, h2, h3]

theorem tz_zB (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) = ((Tu D u : ℕ) : ℝ) := by
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  have hT' : (VS D).hT (Formalism.L2.SG.Pf.Level.toV X (X.zR u)) (Formalism.L2.SG.Pf.Level.toV X (X.zR u)) =
      -(((D.mem u).A.T : ℕ) : D.host.E) := by
    rw [show X.zR u = X.crd (X.zu u) from rfl, Formalism.L2.SG.Pf.Level.toV_crd, X.zu_norm]
  have hι := Formalism.L2.SG.Pf.Level.iota_hE (X := X) (X.zR u) (X.zR u)
  rw [hT'] at hι
  have hJv := Formalism.L2.SG.Pf.Level.hJ_rv (X := X) (vOf X τ) (X.zR u) (X.zR u)
  rw [X.φ_eq, hι] at hJv
  simp only [hJ, map_neg, map_natCast] at hJv
  unfold Formalism.QuantumDeterminants.Tz zB Formalism.QuantumDeterminants.herm
  rw [← hH, Matrix.mulVec_mulVec,
    Matrix.mul_assoc ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ))) (C.Q τ) (C.Qi τ), hQQi,
    Matrix.mul_one, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec, hJv]
  simp [Tu]

end Tr

end Formalism.L2.SG.Pf.LTL
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Parts.DFrameBridge (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  P.FromX → P.Base i0 i0' → ∀ γ h h' : X.B.I.Ginf, IsDFrameX X u u' sc i0 i0' γ h h' → ∀ v,
    Formalism.FourierDecayAlt.D.IsDFrame (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v))
      (trG (P.Q v) (P.Qi v) ((h⁻¹ * γ * h') v))

end Formalism.L2.SG.Pf.Carrier
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def DFrameAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  0 < sc → ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) → ∃ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h'

def Parts.JointTensor (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' →
    ∀ x : ∀ v, X.Vloc u' v,
      (X.piU u h⁻¹) ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
          (X.piU u' h' (X.tensU u' x))) =
        X.tensU u (fun v => P.eP v
          (((((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (P.S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
              (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
            Formalism.FourierDecayAlt.D.vecV (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v)) (P.f (P.τ.symm v))
              (Formalism.FourierDecayAlt.D.toStd P.S.G.r P.S.g 1 (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p)))
            ((P.eQ v).symm (x v))))

end Formalism.L2.SG.Pf.Carrier
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

structure CarrierIn {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Type 1 where
  Wp : InfinitePlace D.host.E → Type
  Wq : InfinitePlace D.host.E → Type
  [pN : ∀ x, NormedAddCommGroup (Wp x)]
  [pI : ∀ x, InnerProductSpace ℂ (Wp x)]
  [qN : ∀ x, NormedAddCommGroup (Wq x)]
  [qI : ∀ x, InnerProductSpace ℂ (Wq x)]
  [pF : ∀ x, FiniteDimensional ℂ (Wp x)]
  [qF : ∀ x, FiniteDimensional ℂ (Wq x)]
  nf : ℕ
  pl : Fin nf ≃ InfinitePlace D.host.E
  emb : Fin nf → (D.host.E →+* ℂ)
  hemb : ∀ v, InfinitePlace.mk (emb v) = pl v
  G : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)
  CA : ℝ
  de : ℕ → ℝ
  de' : ℕ → ℝ
  l : ℕ
  grid : Fin nf → ℕ → Finset ℝ
  grid1 : Fin nf → Finset ℝ
  hv : G.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2
  T : ∀ j : Fin nf, Formalism.FourierDecayAlt.D.LevTower G.k G.r (Wp (pl j)) (Wq (pl j))
  hT : ∀ j, Formalism.QuantumDeterminants.Tz G.k G.r (T j).base.z = ((D.mem u).A.T : ℝ) ∧
    Formalism.QuantumDeterminants.Tz G.k G.r (T j).base.z' = ((D.mem u').A.T : ℝ)
  fc : ∀ j : Fin nf, Formalism.FourierDecayAlt.B.Mat G.k G.r → (Wq (pl j) →L[ℂ] Wp (pl j))
  χ : ℝ → ℝ
  sg : Fin nf → ℂ
  ν' : Fin nf → Fin (2 * G.r + G.k + 1) → ℂ
  m₀ : Fin nf → Formalism.FourierDecayAlt.B.Mat G.k G.r
  top : ∀ j : Fin nf, (Formalism.FourierDecayAlt.B.Mat G.k G.r → (Wq (pl j) →L[ℂ] Wp (pl j))) → List Formalism.FourierDecayAlt.C.Letter →
    Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ
  A₀ : ℝ
  τ : Fin nf ≃ InfinitePlace X.B.I.F
  Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * G.r + G.k + 1)) ℂ
  Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * G.r + G.k + 1)) (Fin X.B.I.n) ℂ
  eP : ∀ v, Wp (pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v
  eQ : ∀ v, Wq (pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v

attribute [instance] CarrierIn.pN CarrierIn.pI CarrierIn.qN CarrierIn.qI CarrierIn.pF CarrierIn.qF

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def sOf (I : CarrierIn X u u') : Formalism.FourierDecayAlt.C.HidaSetting D.host.E I.Wp I.Wq where
  f := I.nf
  pl := I.pl
  emb := I.emb
  hemb := I.hemb
  G := I.G
  CA := I.CA
  de := I.de
  de' := I.de'
  T := ((D.mem u).A.T : ℝ)
  T' := ((D.mem u').A.T : ℝ)
  l := I.l
  grid := I.grid
  grid1 := I.grid1
  pd := fun j => Formalism.FourierDecayAlt.D.componentFamilySetting_ofSetting (I.T j) (I.fc j) I.χ (I.sg j) (I.ν' j) (I.m₀ j) (I.top j)
    ((I.G.g1 * I.G.g2 : ℕ) : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E) 1
  hv := I.hv
  hT := I.hT

structure ModelsFor {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) where
  L : ∀ v : Fin S.f, Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.MA.A (Formalism.FourierDecayAlt.D.parOf S v)
    (Formalism.FourierDecayAlt.MA.DQ (Formalism.FourierDecayAlt.D.parOf S v))) (Formalism.FourierDecayAlt.D.parOf S v).r
  j : ∀ v : Fin S.f, Formalism.FourierDecayAlt.M.Ty (Formalism.FourierDecayAlt.D.parOf S v) →
    Formalism.FourierDecayAlt.MA.SmQ (Formalism.FourierDecayAlt.D.parOf S v).r (Formalism.FourierDecayAlt.D.parOf S v).TT
  lam : ∀ v : Fin S.f, Fin ((Formalism.FourierDecayAlt.D.parOf S v).k + 2 * (Formalism.FourierDecayAlt.D.parOf S v).r + 1) → ℝ
  c : Formalism.FourierDecayAlt.LE.Cut
  Cm : Fin S.f → ℝ
  σ : Fin S.f → ℝ
  Lw : ℕ → Fin S.f → ℝ
  Ll : ℕ → ℕ → Fin S.f → ℝ
  Ll' : ℕ → ℕ → Fin S.f → ℝ

def CarrierOf (I : CarrierIn X u u') (Mo : ModelsFor (sOf I)) : Parts X u u' where
  Wp := I.Wp
  Wq := I.Wq
  S := sOf I
  T := I.T
  f := I.fc
  χ := I.χ
  ν' := I.ν'
  m₀ := I.m₀
  top := I.top
  A₀ := I.A₀
  τ := I.τ
  Q := I.Q
  Qi := I.Qi
  eP := I.eP
  eQ := I.eQ
  L := Mo.L
  j := Mo.j
  lam := Mo.lam
  c := Mo.c
  Cm := Mo.Cm
  σ := Mo.σ
  Lw := Mo.Lw
  Ll := Mo.Ll
  Ll' := Mo.Ll'

end Formalism.L2.SG.Pf.Carrier
end
end
