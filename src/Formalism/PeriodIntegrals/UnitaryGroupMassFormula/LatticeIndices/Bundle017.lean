module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle013
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstCoordsMulVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.ThetaEpsCases
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StKHolds
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle001

@[expose] public section

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix

section Loc

variable {D : D7} (X : HidaSetting D)

def TransA (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
    (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) (π : Op X p →+* ZMod (gOf p)) : Prop :=
  ∀ x : HAp X p, x ∈ KvX X p → ∀ Y : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p),
    ((glRed (algebraMap (Op X p) (FpX X p)) Y : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
        Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) =
      ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
          Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) *
        Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ x) *
        (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) →
    (LocCong X p x ↔ glRed π Y ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k)

def StTransA (p : TypX X) : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧
      ∃ π : Op X p →+* ZMod (gOf p), Function.Surjective π ∧
        RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)} ∧ TransA X p θ Q π

theorem stFrameA_of_trans (hC : LatCoreX) (p : TypX X) (h : StTransA X p) : StFrameA X p := by
  obtain ⟨θ, hθ, Q, hL, π, hπ, hker, hT⟩ := h
  obtain ⟨ψ, hψ, hk, hform⟩ := hC X p θ hθ Q hL (stK_holds X p).choose (stK_holds X p).choose_spec.1
  refine ⟨π, hπ, hker, (stK_holds X p).choose, (stK_holds X p).choose_spec.1, ψ, hψ, hk, 1, fun x => ?_⟩
  rw [map_one, inv_one, one_mul, mul_one]
  have hx : (x : HAp X p) ∈ KvX X p :=
    (Set.ext_iff.mp (stK_holds X p).choose_spec.1 (x : HAp X p)).1 x.2
  exact hT x hx (ψ x) (hform x)

end Loc

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

theorem dual_fwd (hθ : IsSplitEquiv X p θ) (z : Fin X.B.I.n → FpX X p) (hz : z ∈ Mlat2 X p θ) :
    ∀ y ∈ Mlat1 X p θ, z ⬝ᵥ (J1 X p θ *ᵥ y) ∈ OpX X p := by
  intro y hy
  induction hz using Submodule.span_induction with
  | mem z hz' =>
    obtain ⟨l', hl', rfl⟩ := hz'
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨l, hl, rfl⟩ := hy'
      exact dual_gen X p θ hθ l l' hl hl'
    | zero => simp
    | add a b _ _ ha hb =>
      rw [Matrix.mulVec_add]
      first
      | (rw [dotProduct_add]; exact add_mem ha hb)
      | (rw [Matrix.dotProduct_add]; exact add_mem ha hb)
    | smul c a _ ha =>
      show _ ⬝ᵥ (J1 X p θ *ᵥ ((c : FpX X p) • a)) ∈ OpX X p
      rw [Matrix.mulVec_smul]
      first
      | (rw [dotProduct_smul, smul_eq_mul]; exact mul_mem c.2 ha)
      | (rw [Matrix.dotProduct_smul, smul_eq_mul]; exact mul_mem c.2 ha)
  | zero => simp
  | add a b _ _ ha hb =>
    first
    | (rw [add_dotProduct]; exact add_mem ha hb)
    | (rw [Matrix.add_dotProduct]; exact add_mem ha hb)
  | smul c a _ ha =>
    show ((c : FpX X p) • a) ⬝ᵥ _ ∈ OpX X p
    first
    | (rw [smul_dotProduct, smul_eq_mul]; exact mul_mem c.2 ha)
    | (rw [Matrix.smul_dotProduct, smul_eq_mul]; exact mul_mem c.2 ha)

def DualBack : Prop :=
  ∀ z, (∀ y ∈ Mlat1 X p θ, z ⬝ᵥ (J1 X p θ *ᵥ y) ∈ OpX X p) → z ∈ Mlat2 X p θ

theorem latDual_of (hθ : IsSplitEquiv X p θ) (hB : DualBack X p θ) : LatDualP X p θ := by
  first
  | exact fun z => ⟨fun hz => dual_fwd X p θ hθ z hz, hB z⟩
  | exact ⟨fun z hz => dual_fwd X p θ hθ z hz, hB⟩
  | (unfold LatDualP; done)

theorem latBasisAll_of_back
    (hB : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → DualBack X p θ) :
    LatBasisAll X p :=
  latBasisAll_of X p (fun θ hθ => latSplit_of X p θ (unitElt_holds X p θ hθ)) (fun θ _ => latFree_holds X p θ)
    (fun θ hθ => latDual_of X p θ hθ (hB θ hθ))

end Loc

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem pair_sum (v w : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q v ⬝ᵥ crd1 X p θ Q w =
      ∑ i, ∑ j, (θ (v i)).2 * ((θ (inclR (FpX X p) (X.B.I.J i j))).1 * (θ (w j)).1) := by
  unfold crd1 crd2
  rw [Matrix.mulVec_transpose, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp only [dotProduct, Matrix.mulVec, Function.comp_apply]
  rw [← Equiv.sum_comp (idxEquiv X).symm.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.symm_symm, Equiv.symm_apply_apply, fst_apply_alt, snd_apply_alt, jm1, JR, Matrix.map_apply]
  rw [Finset.mul_sum]

theorem pair1 (hθ : IsSplitEquiv X p θ) (v w : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q v ⬝ᵥ crd1 X p θ Q w = (θ (hR (FpX X p) X.B.I.cm.sig X.B.I.J v w)).1 := by
  rw [pair_sum]

  simp only [hR, Formalism.UG.hform, map_sum, Prod.fst_sum, map_mul, Prod.fst_mul, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hθ (v i), Prod.fst_swap]
  ring

theorem pair2 (hθ : IsSplitEquiv X p θ) (v w : Fin X.B.I.n → TpX X p) :
    crd1 X p θ Q v ⬝ᵥ crd2 X p θ Q w = (θ (hR (FpX X p) X.B.I.cm.sig X.B.I.J v w)).2 := by
  rw [dotProduct_comm, pair_sum]

  simp only [hR, Formalism.UG.hform, map_sum, Prod.snd_sum, map_mul, Prod.snd_mul, JR, Matrix.map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hθ (v i), Prod.snd_swap]
  have h := secondEmbedding_eq_star X p θ hθ (X.B.I.J i j)
  rw [herm_entry] at h
  have h' : (θ (inclR (FpX X p) (X.B.I.J i j))).2 = (θ (inclR (FpX X p) (X.B.I.J j i))).1 := h
  rw [h']
  ring

theorem psiV_hA' (x y : Formalism.L2.SG.HidaSetting.VA X.B.I) :
    PI.FinKW.psiV X.B.I p.1 (hA X.B.I x y) =
      hR (FpX X p) X.B.I.cm.sig X.B.I.J (PI.FinKW.vecV X.B.I p.1 x) (PI.FinKW.vecV X.B.I p.1 y) := by
  have hi : ∀ a : X.B.I.E, PI.FinKW.psiV X.B.I p.1 (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) a) =
      inclR (FpX X p) a := by
    intro a
    show (Algebra.TensorProduct.map (evalV X.B.I.F p.1) (AlgHom.id X.B.I.F X.B.I.E))
        ((Algebra.TensorProduct.comm X.B.I.F X.B.I.E (Formalism.MainNotions.S.Af X.B.I.F)) (a ⊗ₜ[X.B.I.F] (1 : Formalism.MainNotions.S.Af X.B.I.F))) =
      (1 : FpX X p) ⊗ₜ[X.B.I.F] a
    rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have hs := PIW.MassDataColumns.psiV_sigA X p

  simp only [hA, hR, Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, JR, PI.FinKW.vecV]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hs, hi]

end Loc

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

theorem frA_int_reindex {F : Type} [Field F] (O : ValuationSubring F) {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) (A : Matrix n n F) (w : m → F) :
    (∀ i, ((Matrix.reindex e.symm e.symm A) *ᵥ w) i ∈ O) ↔ ∀ i, (A *ᵥ (w ∘ e.symm)) i ∈ O := by
  have h : ∀ i, ((Matrix.reindex e.symm e.symm A) *ᵥ w) i = (A *ᵥ (w ∘ e.symm)) (e i) := by
    intro i
    simp only [mulVec, dotProduct, reindex_apply, submatrix_apply, Equiv.symm_symm, Function.comp_apply]
    exact Fintype.sum_equiv e _ _ (fun j => by simp)
  simp only [h]
  constructor
  · intro H j
    simpa using H (e.symm j)
  · intro H i
    exact H (e i)

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem latCrd_of (hL : LatBasis X p θ (reindex₂ X p Q)) (x : Fin X.B.I.n → TpX X p) :
    x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
      IntVec (OvA X p) (crd1 X p θ Q x) ∧ IntVec (OvA X p) (crd2 X p θ Q x) := by
  have hPi : (((reindex₂ X p Q)⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
      Matrix.reindex (idxEquiv X).symm (idxEquiv X).symm
        (((Q⁻¹ : GL (IdxD D) (FpX X p))) : Matrix (IdxD D) (IdxD D) (FpX X p)) := rfl
  have hP : ((reindex₂ X p Q : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
      Matrix.reindex (idxEquiv X).symm (idxEquiv X).symm
        ((Q : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) := rfl
  have hJ : J1 X p θ = jm1 X.B.I.J θ := rfl
  have hv : ∀ w : Fin X.B.I.n → FpX X p,
      (Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ (w ∘ (idxEquiv X).symm) =
        ((jm1 X.B.I.J θ)ᵀ *ᵥ w) ∘ (idxEquiv X).symm := by
    intro w
    rw [Matrix.transpose_reindex, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    congr 2
    funext i
    simp
  rw [hL x]
  unfold IntVec crd1 crd2
  rw [hPi, frA_int_reindex, ← Matrix.mulVec_mulVec, hP, Matrix.transpose_reindex, frA_int_reindex, hJ, ← hv]
  rfl

end Loc

end MassDataIdxSteps
end
end
