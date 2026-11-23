module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgePlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle014
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Trace
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section HS

variable {Wq Wp : Type*} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def cl (U : Wq ≃ₗᵢ[ℂ] Wq) : Wq →L[ℂ] Wq := U.toLinearIsometry.toContinuousLinearMap

theorem cl_apply (U : Wq ≃ₗᵢ[ℂ] Wq) (x : Wq) : cl U x = U x := rfl

theorem sum_inner_eq_trace {ι : Type*} [Fintype ι] (f : OrthonormalBasis ι ℂ Wq) (A B : Wq →L[ℂ] Wp) :
    ∑ i, inner ℂ (B (f i)) (A (f i)) =
      LinearMap.trace ℂ Wq (((ContinuousLinearMap.adjoint B).comp A : Wq →L[ℂ] Wq) : Wq →ₗ[ℂ] Wq) := by
  rw [LinearMap.trace_eq_sum_inner _ f]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ContinuousLinearMap.adjoint_inner_right]

theorem hsInner_comp_isom (A B : Wq →L[ℂ] Wp) (U : Wq ≃ₗᵢ[ℂ] Wq) :
    Formalism.MainNotions.S.hsInner (A.comp (cl U)) (B.comp (cl U)) = Formalism.MainNotions.S.hsInner A B := by
  unfold Formalism.MainNotions.S.hsInner
  calc ∑ i, inner ℂ ((B.comp (cl U)) (stdOrthonormalBasis ℂ Wq i)) ((A.comp (cl U)) (stdOrthonormalBasis ℂ Wq i))
      = ∑ i, inner ℂ (B (((stdOrthonormalBasis ℂ Wq).map U) i)) (A (((stdOrthonormalBasis ℂ Wq).map U) i)) := by
        simp [OrthonormalBasis.map_apply, cl_apply]
    _ = _ := sum_inner_eq_trace _ A B
    _ = ∑ i, inner ℂ (B (stdOrthonormalBasis ℂ Wq i)) (A (stdOrthonormalBasis ℂ Wq i)) :=
        (sum_inner_eq_trace _ A B).symm

theorem hsInner_smul_left (c : ℂ) (A B : Wq →L[ℂ] Wp) :
    Formalism.MainNotions.S.hsInner (c • A) B = c * Formalism.MainNotions.S.hsInner A B := by
  unfold Formalism.MainNotions.S.hsInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem hsInner_smul_right (c : ℂ) (A B : Wq →L[ℂ] Wp) :
    Formalism.MainNotions.S.hsInner A (c • B) = (starRingEnd ℂ) c * Formalism.MainNotions.S.hsInner A B := by
  unfold Formalism.MainNotions.S.hsInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
  ring

theorem hsInner_form (J₁ J₂ : Wq →L[ℂ] Wp) (c₁ c₂ : ℂ) (U₁ U₂ : Wq ≃ₗᵢ[ℂ] Wq) :
    Formalism.MainNotions.S.hsInner (c₁ • J₁.comp (cl U₁)) (c₂ • J₂.comp (cl U₂)) =
      c₁ * (starRingEnd ℂ) c₂ * Formalism.MainNotions.S.hsInner (J₁.comp (cl (U₂.symm.trans U₁))) J₂ := by
  have h : J₁.comp (cl U₁) = (J₁.comp (cl (U₂.symm.trans U₁))).comp (cl U₂) := by
    ext x
    simp [cl_apply]
  rw [hsInner_smul_left, hsInner_smul_right, h, hsInner_comp_isom]
  ring

theorem hsInner_eq_emb {Wq' Wp' : Type} [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] (A B : Wq' →L[ℂ] Wp') :
    Formalism.MainNotions.S.hsInner A B = inner ℂ (Formalism.L2.SG.PackageTie.hsEmb B) (Formalism.L2.SG.PackageTie.hsEmb A) := by
  unfold Formalism.MainNotions.S.hsInner
  simp [Formalism.L2.SG.PackageTie.hsEmb, PiLp.inner_apply]

end HS

section Stmt

variable {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X)

abbrev amp {u u' : D.what₂.Word} (s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') : X.Vpi u' →L[ℂ] X.Vpi u :=
  ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s

abbrev row {u u' : D.what₂.Word} (s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') :=
  rowOf Y.TR (Y.cs u) (Y.cs u') s

def AmpCov : Prop :=
  ∀ (u u' : D.what₂.Word) (t : RT Y u u') (s s' : fib Y t),
    ∃ (c : ℂ) (U : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'), ‖c‖ = 1 ∧ amp Y s'.1 = c • (amp Y s.1).comp (cl U)

def PairAmpConst : Prop :=
  ∀ (u u' : D.what₂.Word) (t₁ t₂ : RT Y u u') (r r' : fib Y t₁ × fib Y t₂),
    row Y r.1.1 = row Y r.2.1 → row Y r'.1.1 = row Y r'.2.1 →
      Formalism.MainNotions.S.hsInner (amp Y r.1.1) (amp Y r.2.1) = Formalism.MainNotions.S.hsInner (amp Y r'.1.1) (amp Y r'.2.1)


variable {Y} in
def FibreCountEq (hF : FinX Y) : Prop :=
  ∀ (u u' : D.what₂.Word) (q : RP Y u u'),
    haveI := hF.fibFT q.1.1
    haveI := hF.fibFT q.1.2
    ∑ r : fib Y q.1.1 × fib Y q.1.2,
      (if row Y r.1.1 = row Y r.2.1 then Formalism.MainNotions.S.wRow D (X.Fu u') r.1.1.lam' else 0) = 1

end Stmt

section Val

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X}

theorem wRow_nonneg {T : D.host.E} (F0 : Formalism.MainNotions.S.FlagG (Formalism.MainNotions.S.VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (Formalism.MainNotions.S.VS D).V) :
    0 ≤ Formalism.MainNotions.S.wRow D F0 Λ := by
  unfold Formalism.MainNotions.S.wRow; exact inv_nonneg.2 (Nat.cast_nonneg _)

theorem lam_eq_of_row {u u' : D.what₂.Word} {s₁ s₂ : _root_.Formalism.L2.SG.PackageTie2.TT Y u u'} (h : row Y s₁ = row Y s₂) :
    s₁.lam = s₂.lam ∧ s₁.lam' = s₂.lam' := by
  unfold row rowOf at h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  exact ⟨h.1, h.2.1⟩

theorem inner_vT {u u' : D.what₂.Word} (s₁ s₂ : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') (h : row Y s₁ = row Y s₂) :
    inner ℂ (vT Y u u' s₂) (vT Y u u' s₁) =
      ((Formalism.MainNotions.S.wRow D (X.Fu u) s₁.lam * Formalism.MainNotions.S.wRow D (X.Fu u') s₁.lam' : ℝ) : ℂ) *
        Formalism.MainNotions.S.hsInner (amp Y s₁) (amp Y s₂) := by
  obtain ⟨hl, hl'⟩ := lam_eq_of_row h
  have hposition : ((⟨s₂.lam, s₂.mem⟩ : {Λ // Λ ∈ Y.what₂ u}), (⟨s₂.lam', s₂.mem'⟩ : {Λ' // Λ' ∈ Y.what₂ u'})) =
      (⟨s₁.lam, s₁.mem⟩, ⟨s₁.lam', s₁.mem'⟩) := by
    simp [hl, hl']
  have hwt : wt s₂ = wt s₁ := by unfold wt; rw [hl, hl']
  have hw2 : wt s₁ * wt s₁ = Formalism.MainNotions.S.wRow D (X.Fu u) s₁.lam * Formalism.MainNotions.S.wRow D (X.Fu u') s₁.lam' :=
    Real.mul_self_sqrt (mul_nonneg (wRow_nonneg _ _) (wRow_nonneg _ _))
  unfold vT vec
  rw [PiLp.inner_apply, Finset.sum_eq_single (⟨s₁.lam, s₁.mem⟩, ⟨s₁.lam', s₁.mem'⟩)]
  · simp only [if_true, hposition, hwt]
    rw [inner_smul_left, inner_smul_right, ← Formalism.L2.SG.Pf.KernelOfEmbedding.hsInner_eq_emb, ← hw2]
    simp only [Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  · intro b _ hb
    simp [hb]
  · intro hb; exact absurd (Finset.mem_univ _) hb

theorem pvR_eq (hF : FinX Y) (hK : PairAmpConst Y) (hN : FibreCountEq hF) {u u' : D.what₂.Word} (q : RP Y u u') :
    pvR hF u u' q = (Formalism.MainNotions.S.wRow D (X.Fu u) q.1.1.lam : ℂ) * Formalism.MainNotions.S.hsInner (amp Y q.l1) (amp Y q.l2) := by
  have key : ∀ r : fib Y q.1.1 × fib Y q.1.2,
      (if rowOf Y.TR (Y.cs u) (Y.cs u') r.1.1 = rowOf Y.TR (Y.cs u) (Y.cs u') r.2.1 then
        inner ℂ (vT Y u u' r.2.1) (vT Y u u' r.1.1) else 0) =
        (Formalism.MainNotions.S.wRow D (X.Fu u) q.1.1.lam : ℂ) * Formalism.MainNotions.S.hsInner (amp Y q.l1) (amp Y q.l2) *
          (((if row Y r.1.1 = row Y r.2.1 then Formalism.MainNotions.S.wRow D (X.Fu u') r.1.1.lam' else 0 : ℝ)) : ℂ) := by
    intro r
    by_cases hr : row Y r.1.1 = row Y r.2.1
    · have hlam : r.1.1.lam = q.1.1.lam := congrArg TermDef.Term.lam r.1.2
      have hc := hK u u' q.1.1 q.1.2 r (q.2.choose, q.2.choose_spec.choose) hr q.2.choose_spec.choose_spec
      rw [if_pos hr, if_pos hr, inner_vT _ _ hr, hc, hlam]
      simp only [RP.l1, RP.l2, Complex.ofReal_mul]
      ring
    · rw [if_neg hr, if_neg hr]
      simp
  unfold pvR
  rw [Finset.sum_congr rfl fun r _ => key r, ← Finset.mul_sum, ← Complex.ofReal_sum]
  have hn := hN u u' q
  rw [hn]
  simp

theorem pvR_form (hF : FinX Y) (hC : AmpCov Y) (hK : PairAmpConst Y) (hN : FibreCountEq hF) {u u' : D.what₂.Word}
    (q : RP Y u u') (g₁ : fib Y q.1.1) (g₂ : fib Y q.1.2) :
    ∃ (c : ℂ) (U : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'), ‖c‖ = 1 ∧
      pvR hF u u' q = (Formalism.MainNotions.S.wRow D (X.Fu u) q.1.1.lam : ℂ) * c *
        Formalism.MainNotions.S.hsInner ((amp Y g₁.1).comp (cl U)) (amp Y g₂.1) := by
  obtain ⟨c₁, U₁, hc₁, h₁⟩ := hC u u' q.1.1 g₁ q.2.choose
  obtain ⟨c₂, U₂, hc₂, h₂⟩ := hC u u' q.1.2 g₂ q.2.choose_spec.choose
  refine ⟨c₁ * (starRingEnd ℂ) c₂, U₂.symm.trans U₁, by simp [hc₁, hc₂], ?_⟩
  rw [pvR_eq hF hK hN q]
  show _ * Formalism.MainNotions.S.hsInner (amp Y q.2.choose.1) (amp Y q.2.choose_spec.choose.1) = _
  rw [h₁, h₂, hsInner_form]
  ring

end Val

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end

section

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut

section Fwd

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem Qi_spanLt (hT : TrHyp F Qm Qim c) {a : ℕ} {v : Fin n → ℂ} (hv : v ∈ spanLt F.e a) :
    ∀ i : Fin (2 * r + k + 1), a ≤ i.val → (Qim *ᵥ v) i = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    intro i hi
    rw [Qi_e hT b]
    have hne : i ≠ Formalism.QuantumDeterminants.eI k r b := fun h => by
      have := congrArg Fin.val h; simp only [Formalism.QuantumDeterminants.eI] at this; simp only [Set.mem_setOf_eq] at hb; omega
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply, hne]
  | zero => intro i _; simp
  | add x y _ _ hx hy => intro i hi; rw [Matrix.mulVec_add, Pi.add_apply, hx i hi, hy i hi, add_zero]
  | smul d x _ hx => intro i hi; rw [Matrix.mulVec_smul, Pi.smul_apply, hx i hi, smul_zero]

theorem e_perp_mid (hT : TrHyp F Qm Qim c) (a : Fin r) (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val)
    (hj2 : j.val ≤ r + k) : hJ ε (F.e a) (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = 0 := by
  have he : F.e a = (c a)⁻¹ • (Qm *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) := by
    rw [hT.he, smul_smul, inv_mul_cancel₀ (c_ne hT a), one_smul]
  have h0 : Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.eI k r a) j = 0 := by
    have ha := a.isLt
    have hsum : a.val + j.val ≠ 2 * r + k := by omega
    unfold Formalism.QuantumDeterminants.Hpk
    simp only [Formalism.QuantumDeterminants.eI, hsum, not_lt.mpr hj1, not_le.mpr ha,
      and_false, false_and, if_false]
  rw [he, PtRepPf.hJ_smul_left, ← herm_Q hT]
  simp only [Formalism.QuantumDeterminants.herm, Formalism.QuantumDeterminants.bvec,
    ← Pi.single_star, star_one, single_dotProduct, Matrix.mulVec_single_one,
    Matrix.col_apply, h0, mul_zero]

theorem fwd_N (hT : TrHyp F Qm Qim c) {g : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ}
    (hgU : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε) (hg : InN ε F.e z g) :
    Qim * g * Qm ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hQQ : Qimᴴ * Qmᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hT.h2, Matrix.conjTranspose_one]
  have hcol : ∀ (j i : Fin (2 * r + k + 1)), (Qim * g * Qm) i j = (Qim *ᵥ (g *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j))) i := by
    intro j i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one]
  refine ⟨?_, fun a i hi => ?_, fun i j hj1 hj2 hi => ?_⟩
  · show (Qim * g * Qm)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qim * g * Qm) = Formalism.QuantumDeterminants.Hpk k r
    rw [← hT.hH]
    calc (Qim * g * Qm)ᴴ * (Qmᴴ * Formalism.REAL.Jm ε * Qm) * (Qim * g * Qm)
        = Qmᴴ * gᴴ * (Qimᴴ * Qmᴴ) * Formalism.REAL.Jm ε * (Qm * Qim) * g * Qm := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Qmᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * Qm := by
          rw [hQQ, hT.h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hgU]
  · rw [hcol, hT.he, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply]
    have hsplit : g *ᵥ F.e a = F.e a + (g - 1) *ᵥ F.e a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hsplit, Matrix.mulVec_add, Pi.add_apply, Qi_spanLt hT (hg.1.1 a) i hi, add_zero, Qi_e hT a,
      Pi.smul_apply, smul_smul, mul_inv_cancel₀ (c_ne hT a), one_smul]
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]
  · rw [hcol]
    have hw : ∀ a, hJ ε (F.e a) (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = 0 := fun a => e_perp_mid hT a j hj1 hj2
    have hsplit : g *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = Qm *ᵥ Formalism.QuantumDeterminants.bvec j + (g - 1) *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hsplit, Matrix.mulVec_add, Pi.add_apply, Qi_spanLt hT (hg.2 _ hw) i hi, add_zero, Matrix.mulVec_mulVec,
      hT.h1, Matrix.one_mulVec]
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]

end Fwd

end Formalism.L2.SG.Pf.Bridge
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.JointPf

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def OOQuot (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) → ∀ y : ∀ v, X.Vloc u' v,
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u);
        Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
          (X.tensU u' y) =
      X.tensU u (fun v => (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
        Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) (y v))

def PlaceJ (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' →
    ∀ (v : InfinitePlace X.B.I.F) (y : X.Vloc u' v),
      X.piLoc u v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u v) v h⁻¹)
        ((haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
          Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v))
          (X.piLoc u' v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u' v) v h') y)) =
      P.eP v
        (((((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (P.S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
            (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
          Formalism.FourierDecayAlt.D.vecV (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v)) (P.f (P.τ.symm v))
            (Formalism.FourierDecayAlt.D.toStd P.S.G.r P.S.g 1 (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p)))
          ((P.eQ v).symm y))

theorem jointTensor_of_steps (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hQ : OOQuot X u u' νq νl) (hP : PlaceJ P sc i0 i0' νl) : P.JointTensor sc i0 i0' νq := by
  unfold Formalism.L2.SG.Pf.Carrier.Parts.JointTensor
  intro p w hpw hγ hG h h' hF x
  rw [X.tensU_equiv, hQ w hγ hG, X.tensU_equiv]
  · exact congrArg (fun f => X.tensU u f) (funext fun v => hP p w hpw hγ hG h h' hF v (x v))
  all_goals
    first
    | exact hF.2.1
    | (intro v y hy
       have h1 := hF.1 v y hy
       nth_rewrite 1 [← h1]
       rw [Matrix.mulVec_mulVec, Pi.inv_apply]
       simp only [uMat]
       rw [← Units.val_mul, ← MulMemClass.coe_mul, inv_mul_cancel, OneMemClass.coe_one, Units.val_one,
         Matrix.one_mulVec])

end Formalism.L2.SG.Pf.Carrier.JointPf
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Built

open Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def chiStd (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

theorem isCut0_chiStd : Formalism.FourierDecayAlt.C6.IsCut0 chiStd := by
  unfold Formalism.FourierDecayAlt.C6.IsCut0
  refine ⟨?_, ⟨1 / 2, by norm_num, fun x hx => ?_⟩, fun x hx => ?_⟩
  · show ContDiff ℝ _ (Real.smoothTransition ∘ fun x : ℝ => 2 * x - 1)
    exact Real.smoothTransition.contDiff.comp (by fun_prop)
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · exact Real.smoothTransition.one_of_one_le (by linarith)

section tower

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def towerOf (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : Formalism.FourierDecayAlt.D.LevTower k r Wp Wq :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose

theorem towerOf_base (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : (towerOf B h1 h2 h3).base = B :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose_spec.1

theorem towerOf_norm (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : Formalism.FourierDecayAlt.D.TowerNormalised (towerOf B h1 h2 h3) :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose_spec.2

end tower

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

abbrev par (I : CarrierIn X u u') (v : Fin I.nf) : Formalism.FourierDecayAlt.M.Par := Formalism.FourierDecayAlt.D.parOf (sOf I) v

def sgOf {nf : ℕ} (G : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (pl : Fin nf ≃ InfinitePlace D.host.E)
    (T T' : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (v : Fin nf) : ℂ :=
  Formalism.FourierDecayAlt.M.sgn ⟨G.k, G.r, T, T', (G.place (pl v)).u de, (G.place (pl v)).u de'⟩ l

theorem sg_of (I : CarrierIn X u u')
    (h : I.sg = sgOf I.G I.pl ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) I.de I.de' (I.l + 1)) :
    ∀ v, I.sg v = Formalism.FourierDecayAlt.M.sgn (par I v) ((sOf I).l + 1) := by
  intro v
  rw [h]
  rfl

def ParNums (I : CarrierIn X u u') : Prop :=
  ∀ v, (∀ i ∈ Finset.Icc 1 (par I v).k, ∃ n : ℤ, (par I v).u i - (par I v).u 1 = n) ∧
    (∀ i ∈ Finset.Icc 1 (par I v).k, ∃ n : ℤ, (par I v).u' i - (par I v).u 1 = n) ∧
    ∀ i ∈ Finset.Icc 1 ((par I v).k - 1), (par I v).lo i ≤ (par I v).hi i

def Types (I : CarrierIn X u u') : Prop :=
  ∀ v, Formalism.FourierDecayAlt.Q.IsType I.G.k I.G.r (I.T v).base.z (I.T v).base.π (par I v).u ∧
    Formalism.FourierDecayAlt.Q.IsType I.G.k I.G.r (I.T v).base.z' (I.T v).base.π' (par I v).u'

def Frames (I : CarrierIn X u u') : Prop := ∀ v, Formalism.FourierDecayAlt.D.IsBaseFrame (I.T v).base (I.ν' v) (I.m₀ v)

def CoefCC (I : CarrierIn X u u') : Prop := ∀ v (m : ℕ), Formalism.FourierDecayAlt.B.InCC I.A₀ m (I.fc v)

def CoefCap (I : CarrierIn X u u') : Prop :=
  ∀ v (Y : ℝ), ∀ g ∈ Formalism.FourierDecayAlt.B.GV I.G.k I.G.r,
    Formalism.FourierDecayAlt.Q.CV I.G.k I.G.r (Y : ℂ) (I.fc v) g = (((sOf I).P v Y : ℝ) : ℂ) • I.fc v g

theorem isPlace_of (I : CarrierIn X u u') (hN : ParNums I) (hty : Types I) (v : Fin I.nf) :
    Formalism.FourierDecayAlt.Q.IsPlace (par I v) (I.T v).base.z (I.T v).base.z' (I.T v).base.π (I.T v).base.π' := by
  unfold Formalism.FourierDecayAlt.Q.IsPlace
  obtain ⟨h1, h2, h3⟩ := hN v
  obtain ⟨t1, t2⟩ := hty v
  obtain ⟨e1, e2⟩ := I.hT v
  have p1 := (I.T v).base.T_pos
  have p2 := (I.T v).base.T'_pos
  rw [e1] at p1
  rw [e2] at p2
  exact ⟨⟨(I.T v).base.k_pos, p1, p2, h1, h2, h3⟩, (I.T v).base.z_mem, (I.T v).base.z'_mem, e1, e2, t1, t2⟩

end Formalism.L2.SG.Pf.Built
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.HostUnramP

open NumberField IsDedekindDomain Formalism.BasicNotions

def HostUnramG : Prop :=
  ∀ D : D7, Formalism.L2.SG.Pf.LocCP.LocTied D → ∀ (p : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin 2),
    ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal → ((D.host.g i : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal ^ 2

theorem gi_val (D : D7) (p : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin 2)
    (hi : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) :
    p.intValuation ((D.host.g i : ℕ) : 𝓞 D.host.F) = WithZero.exp (-1 : ℤ) := by
  exact Formalism.L2.SG.Pf.TypedLoc.tower_val D.host.F D.host.E (D.host.g_prime i) (D.nd.g_split i) p hi

theorem hostUnramG : HostUnramG := by
  intro D _ p i hi hsq
  have h2 := (p.intValuation_le_pow_iff_mem _ 2).mpr hsq
  rw [gi_val D p i hi] at h2
  have h3 := WithZero.exp_le_exp.mp h2
  omega

end Formalism.L2.SG.Pf.HostUnramP
end
end
