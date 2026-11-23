module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstCoordsMulVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondProjSplitMulVec
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
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle001

@[expose] public section

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

def UnitElt : Prop :=
  ∃ a : 𝓞 X.B.I.E, ∃ w ∈ OpX X p, w * (iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E)) = 1

theorem firstSplitCoord_smul (c : FpX X p) (t : TpX X p) : th1 X p θ (c • t) = c * th1 X p θ t := by
  show (θ (c • t)).1 = c * (θ t).1
  rw [map_smul]
  rfl

theorem secondSplitCoord_smul (c : FpX X p) (t : TpX X p) : th2 X p θ (c • t) = c * th2 X p θ t := by
  show (θ (c • t)).2 = c * (θ t).2
  rw [map_smul]
  rfl

theorem osmul_eq (c : OpX X p) (t : TpX X p) : c • t = (c : FpX X p) • t := rfl

theorem th_incl (e : X.B.I.E) : θ (inclR (FpX X p) e) = (iota1 X p θ e, iota2 X p θ e) := rfl

theorem first_raising_mem_equivariant (h : UnitElt X p θ) (l : Fin X.B.I.n → X.B.I.E) (hl : l ∈ X.B.I.L) :
    (fun j => θ.symm (iota1 X p θ (l j), 0)) ∈
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  obtain ⟨a, w, hw, hwa⟩ := h
  have hc2 : iota2 X p θ (a : X.B.I.E) ∈ OpX X p := MassDataIdxLatFree.int_mem (OpX X p) (iota2 X p θ) a
  have heq : (fun j => θ.symm (iota1 X p θ (l j), 0)) =
      (⟨w, hw⟩ : OpX X p) • (ratV (F := X.B.I.F) (FpX X p) (a • l) -
        (⟨iota2 X p θ (a : X.B.I.E), hc2⟩ : OpX X p) • ratV (F := X.B.I.F) (FpX X p) l) := by
    funext j
    apply θ.injective
    rw [AlgEquiv.apply_symm_apply]
    show _ = θ ((w : FpX X p) • (inclR (FpX X p) ((a : X.B.I.E) * l j) -
      (iota2 X p θ (a : X.B.I.E)) • inclR (FpX X p) (l j)))
    rw [map_smul, map_sub, map_smul, map_mul, map_mul]
    simp only [th_incl]
    refine Prod.ext ?_ ?_
    · show iota1 X p θ (l j) = w * (iota1 X p θ (a : X.B.I.E) * iota1 X p θ (l j) -
        iota2 X p θ (a : X.B.I.E) * iota1 X p θ (l j))
      linear_combination (-(iota1 X p θ (l j))) * hwa
    · show (0 : FpX X p) = w * (iota2 X p θ (a : X.B.I.E) * iota2 X p θ (l j) -
        iota2 X p θ (a : X.B.I.E) * iota2 X p θ (l j))
      ring
  rw [heq]
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_))
  · exact Submodule.subset_span ⟨a • l, X.B.I.L.smul_mem a hl, rfl⟩
  · exact Submodule.subset_span ⟨l, hl, rfl⟩

theorem firstLattice_mem_local (h : UnitElt X p θ) (y : Fin X.B.I.n → FpX X p) (hy : y ∈ Mlat1 X p θ) :
    (fun j => θ.symm (y j, 0)) ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact first_raising_mem_equivariant X p θ h l hl
  | zero =>
    convert Submodule.zero_mem (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) using 1 <;> funext j <;> simp
  | add y y' _ _ hy hy' =>
    convert Submodule.add_mem _ hy hy' using 1
    funext j
    simp only [Pi.add_apply]
    rw [← map_add, Prod.mk_add_mk, add_zero]
  | smul c y _ hy =>
    convert Submodule.smul_mem _ c hy using 1
    funext j
    simp only [Pi.smul_apply, osmul_eq X p]
    rw [← map_smul, Prod.smul_mk, smul_zero]
    rfl

theorem secondLattice_mem_local (h : UnitElt X p θ) (z : Fin X.B.I.n → FpX X p) (hz : z ∈ Mlat2 X p θ) :
    (fun j => θ.symm (0, z j)) ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, rfl⟩ := hz
    have h1 := first_raising_mem_equivariant X p θ h l hl
    have h2 : ratV (F := X.B.I.F) (FpX X p) l ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
      Submodule.subset_span ⟨l, hl, rfl⟩
    convert Submodule.sub_mem _ h2 h1 using 1
    funext j
    apply θ.injective
    change θ (θ.symm (0, iota2 X p θ (l j))) = θ (inclR (FpX X p) (l j) - θ.symm (iota1 X p θ (l j), 0))
    rw [map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, th_incl]
    ext <;> simp
  | zero =>
    convert Submodule.zero_mem (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) using 1 <;> funext j <;> simp
  | add y y' _ _ hy hy' =>
    convert Submodule.add_mem _ hy hy' using 1
    funext j
    simp only [Pi.add_apply]
    rw [← map_add, Prod.mk_add_mk, zero_add]
  | smul c y _ hy =>
    convert Submodule.smul_mem _ c hy using 1
    funext j
    simp only [Pi.smul_apply, osmul_eq X p]
    rw [← map_smul, Prod.smul_mk, smul_zero]
    rfl

theorem latSplit_of (h : UnitElt X p θ) : LatSplitP X p θ := by
  unfold LatSplitP
  intro x
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact ⟨Submodule.subset_span ⟨l, hl, rfl⟩, Submodule.subset_span ⟨l, hl, rfl⟩⟩
    | zero =>
      simp only [Pi.zero_apply, map_zero]
      exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add (f := _)]
      exact ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩
    | smul c x _ hx =>
      simp only [Pi.smul_apply, osmul_eq X p, firstSplitCoord_smul, secondSplitCoord_smul]
      exact ⟨Submodule.smul_mem _ c hx.1, Submodule.smul_mem _ c hx.2⟩
  · rintro ⟨h1, h2⟩
    have hx : x = (fun j => θ.symm (th1 X p θ (x j), 0)) + (fun j => θ.symm (0, th2 X p θ (x j))) := by
      funext j
      simp only [Pi.add_apply]
      rw [← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add]
      apply θ.injective
      rw [AlgEquiv.apply_symm_apply]
      rfl
    rw [hx]
    exact Submodule.add_mem _ (firstLattice_mem_local X p θ h _ h1) (secondLattice_mem_local X p θ h _ h2)

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

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem firstCoords_add (a b : Fin X.B.I.n → TpX X p) : crd1 X p θ Q (a + b) = crd1 X p θ Q a + crd1 X p θ Q b := by
  unfold crd1
  rw [map_add (f := _), show (pr1 θ a + pr1 θ b) ∘ (idxEquiv X).symm =
    pr1 θ a ∘ (idxEquiv X).symm + pr1 θ b ∘ (idxEquiv X).symm from rfl, Matrix.mulVec_add]

theorem secondCoords_add (a b : Fin X.B.I.n → TpX X p) : crd2 X p θ Q (a + b) = crd2 X p θ Q a + crd2 X p θ Q b := by
  unfold crd2
  rw [map_add (f := _), show (pr2 θ a + pr2 θ b) ∘ (idxEquiv X).symm =
    pr2 θ a ∘ (idxEquiv X).symm + pr2 θ b ∘ (idxEquiv X).symm from rfl, Matrix.mulVec_add, Matrix.mulVec_add]

theorem firstCoords_tensor_smul (t : TpX X p) (v : Fin X.B.I.n → TpX X p) :
    crd1 X p θ Q (t • v) = (θ t).1 • crd1 X p θ Q v := by
  unfold crd1
  have : pr1 θ (t • v : Fin X.B.I.n → TpX X p) ∘ (idxEquiv X).symm = (θ t).1 • (pr1 θ v ∘ (idxEquiv X).symm) := by
    funext i
    show (θ (t * v ((idxEquiv X).symm i))).1 = (θ t).1 * (θ (v ((idxEquiv X).symm i))).1
    rw [map_mul]; rfl
  rw [this, Matrix.mulVec_smul]

theorem secondCoords_tensor_smul (t : TpX X p) (v : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q (t • v) = (θ t).2 • crd2 X p θ Q v := by
  unfold crd2
  have : pr2 θ (t • v : Fin X.B.I.n → TpX X p) ∘ (idxEquiv X).symm = (θ t).2 • (pr2 θ v ∘ (idxEquiv X).symm) := by
    funext i
    show (θ (t * v ((idxEquiv X).symm i))).2 = (θ t).2 * (θ (v ((idxEquiv X).symm i))).2
    rw [map_mul]; rfl
  rw [this, Matrix.mulVec_smul, Matrix.mulVec_smul]

theorem smulO_eq (c : OvA X p) (v : Fin X.B.I.n → TpX X p) :
    c • v = ((c : FpX X p) • v) := rfl

end Loc

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

def fposA (a : Fin D.R.rS) : IdxD D := Sum.inr (Sum.inr (Fin.rev a))

def EntA (π : Op X p →+* ZMod (gOf p)) (Y : GL (IdxD D) (Op X p)) : Prop :=
  (∀ a : Fin D.R.rS, ∀ i, i ∉ (Sum.inl '' {b : Fin D.R.rS | b.1 < a.1} : Set (IdxD D)) →
    π ((Y : Matrix (IdxD D) (IdxD D) (Op X p)) i (Sum.inl a)) = if i = Sum.inl a then 1 else 0) ∧
  (∀ i, i ∉ (Sum.inl '' Set.univ : Set (IdxD D)) →
    π ((Y : Matrix (IdxD D) (IdxD D) (Op X p)) i zI) = if i = zI then 1 else 0) ∧
  (∀ j : Fin D.R.k, ∀ i, i ∉ (posW (r := D.R.rS) j : Set (IdxD D)) →
    π ((Y : Matrix (IdxD D) (IdxD D) (Op X p)) i (wI j)) = if i = wI j then 1 else 0) ∧
  (∀ a : Fin D.R.rS, ∀ i, i ∉ (fposA (D := D) '' {b : Fin D.R.rS | b.1 < a.1}) →
    π (((Y⁻¹ : GL (IdxD D) (Op X p)) : Matrix (IdxD D) (IdxD D) (Op X p)) (fposA a) i) =
      if i = fposA a then 1 else 0) ∧
  (∀ i, i ∉ (fposA (D := D) '' Set.univ) →
    π (((Y⁻¹ : GL (IdxD D) (Op X p)) : Matrix (IdxD D) (IdxD D) (Op X p)) zI i) = if i = zI then 1 else 0)

theorem firstCoords_sub (a b : Fin X.B.I.n → TpX X p) : crd1 X p θ Q (a - b) = crd1 X p θ Q a - crd1 X p θ Q b := by
  unfold crd1
  rw [map_sub, show (pr1 θ a - pr1 θ b) ∘ (idxEquiv X).symm =
    pr1 θ a ∘ (idxEquiv X).symm - pr1 θ b ∘ (idxEquiv X).symm from rfl, Matrix.mulVec_sub]

theorem secondCoords_sub (a b : Fin X.B.I.n → TpX X p) : crd2 X p θ Q (a - b) = crd2 X p θ Q a - crd2 X p θ Q b := by
  unfold crd2
  rw [map_sub, show (pr2 θ a - pr2 θ b) ∘ (idxEquiv X).symm =
    pr2 θ a ∘ (idxEquiv X).symm - pr2 θ b ∘ (idxEquiv X).symm from rfl, Matrix.mulVec_sub, Matrix.mulVec_sub]

end Loc

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
open scoped TensorProduct

theorem frA_reindex_mul {R m n : Type} [CommRing R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (A B : Matrix m m R) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B :=
  (Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm).symm

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem secondCoords_mulVec (hθ : IsSplitEquiv X p θ) (x : HAp X p) (Z : Matrix (IdxD D) (IdxD D) (FpX X p))
    (hZ : Z * (((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ x) *
        (Q : Matrix (IdxD D) (IdxD D) (FpX X p))) = 1) (v : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q (((HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J x : GL (Fin X.B.I.n) (TpX X p)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) *ᵥ v) = Zᵀ *ᵥ crd2 X p θ Q v := by
  set e := idxEquiv X
  set M1 := Matrix.reindex e e (cmp1 X.B.I.cm.sig X.B.I.J θ x) with hM1
  set M2 := Matrix.reindex e e (cmp2 X.B.I.cm.sig X.B.I.J θ x) with hM2
  set J' := Matrix.reindex e e (jm1 X.B.I.J θ) with hJ'
  set Qm := (Q : Matrix (IdxD D) (IdxD D) (FpX X p))
  set Qi := ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p))
  have hQ : Qm * Qi = 1 := by
    simp only [Qm, Qi]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hU : M1ᵀ * (J'ᵀ * M2) = J'ᵀ := by
    have h0 := cmp_unit X.B.I.cm.sig X.B.I.J θ hθ x
    have h1 := congrArg (fun A => Matrix.reindex e e Aᵀ) h0
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h1
    rw [frA_reindex_mul, frA_reindex_mul] at h1
    simpa [hM1, hM2, hJ', Matrix.transpose_reindex] using h1
  have hYZ : (Qi * M1 * Qm) * Z = 1 := mul_eq_one_comm.mp hZ
  have hQY : Qm * (Qi * M1 * Qm) = M1 * Qm := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
  have key : Qmᵀ * (J'ᵀ * M2) = Zᵀ * (Qmᵀ * J'ᵀ) := by
    calc Qmᵀ * (J'ᵀ * M2) = ((Qi * M1 * Qm) * Z)ᵀ * (Qmᵀ * (J'ᵀ * M2)) := by
          rw [hYZ, Matrix.transpose_one, Matrix.one_mul]
      _ = Zᵀ * ((Qm * (Qi * M1 * Qm))ᵀ * (J'ᵀ * M2)) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul Qm]; simp only [Matrix.mul_assoc]
      _ = Zᵀ * (Qmᵀ * (M1ᵀ * (J'ᵀ * M2))) := by
          rw [hQY, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Zᵀ * (Qmᵀ * J'ᵀ) := by rw [hU]
  unfold crd2
  rw [secondProj_split_mulVec]
  have hr : ((((HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J x : GL (Fin X.B.I.n) (TpX X p)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)).map fun t => (θ t).2) *ᵥ pr2 θ v) ∘ e.symm =
      M2 *ᵥ (pr2 θ v ∘ e.symm) := by
    rw [hM2, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    have : (pr2 θ v ∘ e.symm) ∘ e.symm.symm = pr2 θ v := by funext i; simp
    rw [this]; rfl
  have key' : Qmᵀ * J'ᵀ * M2 = Zᵀ * Qmᵀ * J'ᵀ := by rw [Matrix.mul_assoc, key, Matrix.mul_assoc]
  rw [hr, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun A => A *ᵥ (pr2 θ v ∘ e.symm)) key'

end Loc

end MassDataIdxSteps
end
end
