module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle299
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Formalism.RealPlaceAnalysis.Bundle002
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle768
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle839
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle782
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle013
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle004
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OpenKer

open GlobalTheory.AdelicU Filter Topology

theorem eq_one_on_finite_of_mul : ∀ {D : D7} (T : HSp D) (K : Subgroup (GA D T)), IsOpen (K : Set (GA D T)) → ∀ F : GA D T → ℂ, Continuous F → F 1 = 1 → (∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b) → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → F k = 1 := by
  intro D T K hK F hF h1 hmul
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin D.sp.cm.sig T.gram
  have hc := continuous_ofFin D.sp.cm.sig T.gram
  have hN : {y | ‖F (ofFin D.sp.cm.sig T.gram y) - 1‖ < 1 / 2} ∈ 𝓝 (1 : GFin D.sp.cm.sig T.gram) :=
    (isOpen_lt (continuous_norm.comp ((hF.comp hc).sub continuous_const)) continuous_const).mem_nhds
      (by simp [h1])
  have hK' : {y | ofFin D.sp.cm.sig T.gram y ∈ K} ∈ 𝓝 (1 : GFin D.sp.cm.sig T.gram) :=
    (hK.preimage hc).mem_nhds (by simp [one_mem])
  obtain ⟨W, hW⟩ := NonarchimedeanGroup.is_nonarchimedean _ (inter_mem hN hK')
  refine ⟨W.toSubgroup.comap (projFin D.sp.cm.sig T.gram),
    W.isOpen.preimage (continuous_projFin D.sp.cm.sig T.gram), ?_⟩
  intro k hk hkf
  have hkk : ∀ n : ℕ, ofFin D.sp.cm.sig T.gram (projFin D.sp.cm.sig T.gram (k ^ n)) = k ^ n := fun n => by
    have h := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig T.gram (k ^ n)
    rwa [mem_finPts.1 (pow_mem hkf n), map_one, one_mul] at h
  have hW' : ∀ n : ℕ, ‖F (k ^ n) - 1‖ < 1 / 2 ∧ k ^ n ∈ K := fun n => by
    have : projFin D.sp.cm.sig T.gram (k ^ n) ∈ W := by
      rw [map_pow]; exact pow_mem (show projFin D.sp.cm.sig T.gram k ∈ W from hk) n
    have h := hW this
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hkk n] at h
    exact h
  have hpow : ∀ n : ℕ, F (k ^ n) = F k ^ n := fun n => by
    induction n with
    | zero => simp [h1]
    | succ n ih =>
      rw [pow_succ, hmul _ (hW' n).2 (pow_mem hkf n) _ (by simpa using (hW' 1).2) hkf, ih, pow_succ]
  exact GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le fun m => by
    rw [← hpow]; exact (hW' m).1.le

end GlobalTheory.OpenKer
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParabolicDatum

section Ring

variable {κ : Type} [CommRing κ] {a b r : ℕ}

theorem tri_zero {n : ℕ} {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) (i j : Fin n) (hi : r ≤ i.val) (hj : j.val < r) :
    g.val i j = 0 := by
  rw [Formalism.L2.DIV.mem_blockTri] at hg
  apply hg
  simp only [Formalism.L2.DIV.blk2, if_pos hj, if_neg (not_lt.mpr hi)]
  exact Nat.zero_lt_one

theorem lowZero_mul {c : ℕ} {x : Matrix (Fin c) (Fin b) κ} {y : Matrix (Fin b) (Fin a) κ}
    (hx : LowZero r x) (hy : LowZero r y) : LowZero r (x * y) := by
  intro i j hi hj
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l.val < r
  · rw [hx i l hi hl, zero_mul]
  · rw [hy l j (not_lt.mp hl) hj, mul_zero]

theorem lowZero_of_tri {n : ℕ} {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) : LowZero r g.val := fun i j hi hj => tri_zero hg i j hi hj

theorem topL_eq (ha : r ≤ a) (hb : r ≤ b) (y : Matrix (Fin b) (Fin a) κ) :
    topL r y = y.submatrix (Fin.castLE hb) (Fin.castLE ha) := by
  ext i j
  have hij : i.val < b ∧ j.val < a := ⟨lt_of_lt_of_le i.isLt hb, lt_of_lt_of_le j.isLt ha⟩
  simp only [topL, dif_pos hij, Matrix.submatrix_apply]
  rfl

theorem topL_mul {c : ℕ} (ha : r ≤ a) (hb : r ≤ b) (hc : r ≤ c) (x : Matrix (Fin c) (Fin b) κ)
    {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero r y) : topL r (x * y) = topL r x * topL r y := by
  rw [topL_eq ha hc, topL_eq hb hc, topL_eq ha hb]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hb) (Fin.castLE_injective hb) _ _ ?_ fun l => rfl
  intro l hl
  have hrl : r ≤ l.val := by
    by_contra hlt
    exact hl ⟨⟨l.val, not_le.mp hlt⟩, rfl⟩
  rw [hy l _ hrl (by simp), mul_zero]

theorem topL_tri {n : ℕ} (hn : r ≤ n) {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) :
    topL r g.val = (upperLeftBlock hn g).val := by
  rw [topL_eq hn hn, Formalism.L2.DIV.upper_block_val_submatrix hn hg]

theorem det_blockTriangular_eq_mul_diagBlocks {n : ℕ} (hn : r ≤ n) {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) :
    Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hn g) * dBlk (blk2 r) 1 g := by
  apply Units.ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Formalism.L2.DIV.upper_block_val_submatrix hn hg, Formalism.L2.DIV.diag_block_det_val 1 hg,
    Matrix.twoBlockTriangular_det (g : Matrix (Fin n) (Fin n) κ) (fun i : Fin n => i.val < r)
      (fun i hi j hj => tri_zero hg i j (not_lt.mp hi) hj)]
  congr 1
  · let e : Fin r ≃ {i : Fin n // i.val < r} :=
      ⟨fun i => ⟨Fin.castLE hn i, i.isLt⟩, fun i => ⟨i.1.val, i.2⟩, fun _ => rfl, fun _ => rfl⟩
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl
  · let e : {i : Fin n // Formalism.L2.DIV.blk2 r i = 1} ≃ {i : Fin n // ¬ i.val < r} :=
      Equiv.subtypeEquivRight fun i => by
        unfold Formalism.L2.DIV.blk2
        split_ifs with h <;> simp [h]
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl

theorem lowZero_move {G : GL (Fin a) κ} {H : GL (Fin b) κ} (hG : G ∈ blockTri (blk2 r)) (hH : H ∈ blockTri (blk2 r))
    (y : Matrix (Fin b) (Fin a) κ) : LowZero r ((H⁻¹).val * y * G.val) ↔ LowZero r y := by
  constructor
  · intro h
    have hy : y = H.val * ((H⁻¹).val * y * G.val) * (G⁻¹).val := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        Units.mul_inv, Matrix.mul_one]
    rw [hy]
    exact lowZero_mul (lowZero_mul (lowZero_of_tri hH) h) (lowZero_of_tri (Subgroup.inv_mem _ hG))
  · intro h
    exact lowZero_mul (lowZero_mul (lowZero_of_tri (Subgroup.inv_mem _ hH)) h) (lowZero_of_tri hG)

theorem det_topL_move (ha : r ≤ a) (hb : r ≤ b) {G : GL (Fin a) κ} {H : GL (Fin b) κ} (hG : G ∈ blockTri (blk2 r))
    (hH : H ∈ blockTri (blk2 r)) {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero r y) :
    (topL r ((H⁻¹).val * y * G.val)).det =
      ((Matrix.GeneralLinearGroup.det G * (dBlk (blk2 r) 1 G)⁻¹ *
        ((Matrix.GeneralLinearGroup.det H)⁻¹ * dBlk (blk2 r) 1 H) : κˣ) : κ) * (topL r y).det := by
  have hHi : H⁻¹ ∈ blockTri (blk2 r) := Subgroup.inv_mem _ hH
  have e1 : topL r ((H⁻¹).val * y * G.val) = (upperLeftBlock hb H⁻¹).val * topL r y * (upperLeftBlock ha G).val := by
    rw [topL_mul ha ha hb _ (lowZero_of_tri hG), topL_mul ha hb hb _ hy, topL_tri hb hHi, topL_tri ha hG]
  have key : (Matrix.GeneralLinearGroup.det G * (dBlk (blk2 r) 1 G)⁻¹ *
      ((Matrix.GeneralLinearGroup.det H)⁻¹ * dBlk (blk2 r) 1 H) : κˣ) =
      Matrix.GeneralLinearGroup.det (upperLeftBlock hb H⁻¹) * Matrix.GeneralLinearGroup.det (upperLeftBlock ha G) := by
    have dG := det_blockTriangular_eq_mul_diagBlocks ha hG
    have dH := det_blockTriangular_eq_mul_diagBlocks hb hHi
    have dinv : dBlk (blk2 r) 1 H⁻¹ = (dBlk (blk2 r) 1 H)⁻¹ :=
      Formalism.L2.DIV.extendOne_inv (Formalism.L2.DIV.blkDet (blk2 r) 1) hH
    rw [map_inv, dinv] at dH
    rw [dG, dH, mul_inv_cancel_right, inv_mul_cancel_right, mul_comm]
  rw [e1, Matrix.det_mul, Matrix.det_mul, key, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply]
  ring

end Ring

theorem omegaQ_parabolic : ∀ (D : D7) (a b r : ℕ), r ≤ a → r ≤ b → ∀ (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (n : ℤ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Q, G PP ∈ blockTri (blk2 r) ∧ H PP ∈ blockTri (blk2 r)) → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaQ Q r ξ n (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val) = ((∏ PP ∈ Q, (ξ PP (Matrix.GeneralLinearGroup.det (G PP)) * (ξ PP (dBlk (blk2 r) 1 (G PP)))⁻¹ * ((ξ PP (Matrix.GeneralLinearGroup.det (H PP)))⁻¹ * ξ PP (dBlk (blk2 r) 1 (H PP)))) ^ n : ℂˣ) : ℂ) * omegaQ Q r ξ n y := by
  intro D a b r ha hb Q ξ n G H hGH y
  have hdet : ∀ PP ∈ Q, LowZero r (y PP) →
      (topL r (((H PP)⁻¹).val * y PP * (G PP).val)).det =
        ((Matrix.GeneralLinearGroup.det (G PP) * (dBlk (blk2 r) 1 (G PP))⁻¹ *
          ((Matrix.GeneralLinearGroup.det (H PP))⁻¹ * dBlk (blk2 r) 1 (H PP)) : (kP PP)ˣ) : kP PP) *
          (topL r (y PP)).det :=
    fun PP hP hy => det_topL_move ha hb (hGH PP hP).1 (hGH PP hP).2 hy
  have hcond : (∀ PP ∈ Q, LowZero r (((H PP)⁻¹).val * y PP * (G PP).val) ∧
      IsUnit (topL r (((H PP)⁻¹).val * y PP * (G PP).val)).det) ↔
      ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det := by
    refine forall₂_congr fun PP hP => ?_
    rw [lowZero_move (hGH PP hP).1 (hGH PP hP).2 (y PP)]
    refine and_congr_right fun hy => ?_
    rw [hdet PP hP hy]
    exact Units.isUnit_units_mul _ _
  unfold omegaQ
  split_ifs with h1 h2 h2
  · simp only [← Units.val_zpow_eq_zpow_val, ← Units.coe_prod, ← Units.val_mul]
    congr 1
    rw [← Finset.prod_attach Q, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [← mul_zpow]
    congr 1
    have hu : (h1 PP.1 PP.2).2.unit =
        (Matrix.GeneralLinearGroup.det (G PP.1) * (dBlk (blk2 r) 1 (G PP.1))⁻¹ *
          ((Matrix.GeneralLinearGroup.det (H PP.1))⁻¹ * dBlk (blk2 r) 1 (H PP.1))) * (h2 PP.1 PP.2).2.unit := by
      ext
      rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]
      exact hdet PP.1 PP.2 (h2 PP.1 PP.2).1
    rw [hu]
    simp only [map_mul, map_inv]
  · exact absurd (hcond.mp h1) h2
  · exact absurd (hcond.mpr h2) h1
  · rw [mul_zero]

end GlobalTheory.ParabolicDatum
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.discrete_series_model_of_dual_parameter : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S), ∃ (M' : DSModel V (fun τ => dualPar (S τ))) (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w) := by
  first | exact @GlobalTheory.ConjDS.exists_conjModel | exact GlobalTheory.ConjDS.exists_conjModel | (intros; apply GlobalTheory.ConjDS.exists_conjModel <;> assumption)
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.Proof.GenericSubmoduleMonomials

noncomputable def genSub (n n' k : ℕ) : MvPolynomial (Fin n' × Fin k) ℂ →ₐ[ℂ]
    MvPolynomial (Fin n × Fin k) (MvPolynomial (Fin n' × Fin n) ℂ) :=
  aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (X (v.1, t)) * X (t, v.2))

theorem map_eval_genSub (n n' k : ℕ) (x : Matrix (Fin n') (Fin n) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ) :
    map (eval (fun v : Fin n' × Fin n => x v.1 v.2)) (genSub n n' k f) =
      aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ)) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [genSub, aeval_C, aeval_C]
    simp [MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    have hv : map (eval (fun v : Fin n' × Fin n => x v.1 v.2)) (genSub n n' k (X v)) =
        ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ) := by

      rw [genSub, aeval_X, map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_mul, map_C, map_X, eval_X]
    rw [map_mul, map_mul, hp, map_mul, hv, aeval_X]

theorem repr_basisMonomials {σ : Type} (φ : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    (basisMonomials σ ℂ).repr φ m = AddMonoidAlgebra.coeff φ m := rfl

theorem exists_pairing : ∀ (n n' k : ℕ), ∃ T : MvPolynomial (Fin n × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n) ℂ, ∀ (φ : MvPolynomial (Fin n × Fin k) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ) (x : Matrix (Fin n') (Fin n) ℂ), eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ)) f)) := by
  intro n n' k
  refine ⟨(basisMonomials (Fin n × Fin k) ℂ).constr ℂ (fun m => ((∏ j ∈ m.support, (m j).factorial : ℕ) : ℂ) •
    (((lcoeff (MvPolynomial (Fin n' × Fin n) ℂ) m).restrictScalars ℂ) ∘ₗ (genSub n n' k).toLinearMap)), ?_⟩
  intro φ f x
  have hs : ((basisMonomials (Fin n × Fin k) ℂ).repr φ).support = φ.support := by
    ext m
    rw [Finsupp.mem_support_iff, repr_basisMonomials, mem_support_iff]

  rw [Module.Basis.constr_apply, Finsupp.sum, hs, fockF, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [repr_basisMonomials, ← map_eval_genSub, coeff_map, coeff_map]
  simp only [LinearMap.smul_apply, smul_eval, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.restrictScalars_apply, lcoeff_apply, starRingEnd_apply, star_star]
  ring

end GlobalTheory.Proof.GenericSubmoduleMonomials
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.SmallerSource

theorem discrete_series_gk_admissible_irreducible (X : ProvA) (h5 : admQ5 X) {r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) :
    AdmGK (X.ds r s lam).HK ∧ IrrGK (X.ds r s lam).HK := by
  obtain ⟨hU, -, -⟩ := h5 r s hrs
  set D := X.ds r s lam
  exact (hU D.U ⟨D.nontriv, D.irred⟩).2.2 D.HK D.ι ⟨D.ι_inj, D.ι_range, D.der⟩

theorem cPair_sub {p q i : ℕ} (hp : i ≤ p) (hq : i ≤ q) : cPair (p - i) (q - i) = cPair p q := by
  unfold cPair
  rw [Nat.cast_sub hp, Nat.cast_sub hq]
  ring

theorem intw_eq_zero (X : ProvA) (h2 : admH2 X) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair p q) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair p q) (blattner lam) a ≤ 0))
    (hno : ∀ μ, ¬ JointShape p q r s μ (blattner lam))
    (MM : GKMod p q) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ MM.V (X.ds r s lam).HK.V)
    (hf : IsIntw (X.fock p q r s) MM (X.ds r s lam).HK f) : f = 0 := by
  by_contra hf0

  have hAI := discrete_series_gk_admissible_irreducible X h5 hrs lam
  have hI : Intw MM (X.ds r s lam).HK f := (isIntw_iff (X.fock p q r s) MM _ f).1 hf
  obtain ⟨hfin, -, hcone⟩ := hD r s lam hlam

  have hex : ∃ v, IsHW (X.ds r s lam).HK.act (blattner lam) v := by
    have hne : hwSub (X.ds r s lam).HK.act (blattner lam) ≠ ⊥ := by
      intro h
      rw [h] at hfin
      simp at hfin
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨v, hv0, hv⟩

  have hmin : ∀ ν w, IsHW (X.ds r s lam).HK.act ν w →
      degW (cPair p q) (blattner lam) ≤ degW (cPair p q) ν :=
    GlobalTheory.T.degW_blattner_le_of_blattnerCone r s (X.ds r s lam).HK lam (cPair p q) θ hcone hsign

  obtain ⟨⟨μ, P, hPJ, hP1, hP2, hfP⟩, -⟩ :=
    GlobalTheory.T.fock_minimal_KType_second_member p q r s MM (X.ds r s lam).HK f hAI.2 hAI.1 hI hf0 (blattner lam) hex hmin

  have hbot := ((h2 p q r s).2.2.2.2.1 μ (blattner lam)).2 (hno μ)
  have hmem : P ∈ hwSub (X.fock p q r s).act1 μ ⊓ hwSub (X.fock p q r s).act2 (blattner lam) ⊓
      Submodule.span ℂ (X.fock p q r s).J := by
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hP1.2, hP2.2⟩, ?_⟩
    rw [J_eq (X.fock p q r s)]
    exact Submodule.subset_span hPJ
  rw [hbot] at hmem
  exact hP1.1 ((Submodule.mem_bot ℂ).1 hmem)

theorem no_map_smaller_source :
    ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFifth X := by
  intro X _ h2 hD h5
  unfold ArchimedeanRallisFifth ARv DataAR DataARm
  constructor
  ·
    intro t al be ga de hd hne i hi1 hip hiq MM f hf
    have hA := hd.1
    have ht : 1 ≤ t := by
      unfold HypA at hA
      exact hA.1
    obtain ⟨-, -, hlam', -, hs'⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
    have hno := ((GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi1).2.2 hne hip hiq).1
    refine intw_eq_zero X h2 hD h5 (by omega) (lamA' t al be ga de) hlam' ((t : ℚ) / 2) ?_ hno MM f hf
    rw [cPair_sub hip hiq]
    exact hs'
  ·
    intro t al be ga de hd hne i hi1 hip hiq MM f hf
    have hA := hd.1
    have ht : 1 ≤ t := by
      unfold HypA at hA
      exact hA.1
    obtain ⟨-, hlam', -, hs'⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hA
    have hno := ((GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi1).2.2 hne hip hiq).2
    refine intw_eq_zero X h2 hD h5 (by omega) (lamM' t al be ga de) hlam' ((t : ℚ) / 2) ?_ hno MM f hf
    rw [cPair_sub hip hiq]
    exact hs'

end GlobalTheory.SmallerSource
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open Filter Topology

namespace GlobalTheory.RootEx.OpenKernel


open MeasureTheory ValuativeRel Matrix in
open Filter Topology in
theorem _root_.GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar {k : Type} [Field k]
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    IsLocallyConstant (fun x : k => (ψ x : ℂ)) := by
  by_cases h : ψ = 1
  · subst h
    simp only [AddChar.one_apply, Circle.coe_one]
    exact IsLocallyConstant.const 1
  · obtain ⟨c, hc⟩ := _root_.GlobalTheory.SplitWeil.exists_hasConductor_of_continuous ψ hψ h
    exact (_root_.GlobalTheory.SplitWeil.HasConductor.isLocallyConstant hc).comp _


open MeasureTheory ValuativeRel Matrix in
open Filter Topology in
theorem _root_.GlobalTheory.RootEx.OpenKernel.characters_locallyConstant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ μ : kˣ →* ℂˣ, Continuous μ → IsOpen (μ.ker : Set kˣ)) ∧ ∀ ψ : AddChar k Circle, Continuous ψ → IsLocallyConstant (fun x : k => (ψ x : ℂ)) :=
  fun _ _ _ _ _ => ⟨fun μ hμ => _root_.GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous μ hμ,
    fun ψ hψ => _root_.GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψ hψ⟩

end GlobalTheory.RootEx.OpenKernel
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.not_locallyFinite_quadraticMul_add_degreeNonraising : ∀ (σ : Type) [Finite σ] (Q : MvPolynomial σ ℂ) (L : Module.End ℂ (MvPolynomial σ ℂ)), Q ≠ 0 → Q.IsHomogeneous 2 → (∀ P, (L P).totalDegree ≤ P.totalDegree) → ∀ φ : MvPolynomial σ ℂ, φ ≠ 0 → ∀ F : Submodule ℂ (MvPolynomial σ ℂ), FiniteDimensional ℂ F → ¬ ∀ n : ℕ, ((LinearMap.mulLeft ℂ Q + L) ^ n) φ ∈ F := by
  first | exact @GlobalTheory.Chain.RealIt.not_locallyFinite_mulLeft_add | exact GlobalTheory.Chain.RealIt.not_locallyFinite_mulLeft_add | (intros; apply GlobalTheory.Chain.RealIt.not_locallyFinite_mulLeft_add <;> assumption)
end
