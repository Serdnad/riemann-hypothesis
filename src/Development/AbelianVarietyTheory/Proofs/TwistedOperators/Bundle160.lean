module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle994
import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesIntegrableCoefficientProjector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceFockDsUniqueness
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle149
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle010
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OmegaTwistLaw

section Fin
variable {κ : Type} [CommRing κ]

theorem lowZero_mul {a b c r : ℕ} {A : Matrix (Fin b) (Fin c) κ} {B : Matrix (Fin c) (Fin a) κ}
    (hA : LowZero r A) (hB : LowZero r B) : LowZero r (A * B) := by
  intro i j hi hj
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases le_or_gt r l.val with hl | hl
  · rw [hB l j hl hj, mul_zero]
  · rw [hA i l hi hl, zero_mul]

theorem topL_eq {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) (A : Matrix (Fin b) (Fin a) κ) :
    topL r A = A.submatrix (Fin.castLE hb) (Fin.castLE ha) := by
  ext i j
  have hij : i.val < b ∧ j.val < a := ⟨lt_of_lt_of_le i.isLt hb, lt_of_lt_of_le j.isLt ha⟩
  show (if h : i.val < b ∧ j.val < a then A ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else 0) = A (Fin.castLE hb i) (Fin.castLE ha j)
  rw [dite_eq_left hij]
  rfl

theorem topL_mul {a b c r : ℕ} (ha : r ≤ a) (hb : r ≤ b) (hc : r ≤ c) (A : Matrix (Fin b) (Fin c) κ)
    {B : Matrix (Fin c) (Fin a) κ} (hB : LowZero r B) : topL r (A * B) = topL r A * topL r B := by
  rw [topL_eq ha hb, topL_eq hc hb, topL_eq ha hc]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hc) (Fin.castLE_injective hc) _ _ (fun l hl => ?_) (fun l => rfl)
  have hlr : r ≤ l.val := by
    by_contra hlt
    exact hl ⟨⟨l.val, not_le.mp hlt⟩, Fin.ext rfl⟩
  rw [hB l _ hlr (by simp), mul_zero]

theorem lowZero_of_mem {n r : ℕ} {g : GL (Fin n) κ} (h : g ∈ blockTri (blk2 r)) : LowZero r g.val := by
  intro i j hi hj
  refine mem_blockTri.mp h i j ?_
  have h1 : blk2 r i = 1 := if_neg (not_lt.mpr hi)
  have h0 : blk2 r j = 0 := if_pos hj
  rw [h0, h1]
  exact Nat.zero_lt_one

theorem det_eq {n r : ℕ} (hr : r ≤ n) {g : GL (Fin n) κ} (h : g ∈ blockTri (blk2 r)) :
    Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) * dBlk (blk2 r) 1 g := by
  have hg : (g.val).BlockTriangular (blk2 r) := fun i j hij => mem_blockTri.mp h i j hij
  let e : Fin r ≃ {x : Fin n // blk2 r x = 0} :=
    { toFun := fun i => ⟨Fin.castLE hr i, if_pos (by simp)⟩
      invFun := fun x => ⟨x.1.val, by
        have hx := x.2
        unfold blk2 at hx
        split_ifs at hx with hlt
        exact hlt⟩
      left_inv := fun i => Fin.ext rfl
      right_inv := fun x => Subtype.ext (Fin.ext rfl) }
  have hsub : (g.val.toSquareBlock (blk2 r) 0).submatrix e e = g.val.submatrix (Fin.castLE hr) (Fin.castLE hr) := by
    ext i j
    rfl
  ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    upper_block_val_submatrix hr h, diag_block_det_val 1 h, hg.det, ← hsub, Matrix.det_submatrix_equiv_self]
  have hsub2 : Finset.univ.image (blk2 (n := n) r) ⊆ {0, 1} := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    unfold blk2
    split_ifs <;> simp
  rw [Finset.prod_subset hsub2 (fun x _ hx => ?_), Finset.prod_pair zero_ne_one]
  · rfl
  · haveI : IsEmpty {y : Fin n // blk2 r y = x} :=
      ⟨fun y => hx (Finset.mem_image.mpr ⟨y.1, Finset.mem_univ _, y.2⟩)⟩
    exact Matrix.det_isEmpty

theorem det_topL {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) {gS : GL (Fin a) κ} {gT : GL (Fin b) κ}
    (hS : gS ∈ blockTri (blk2 r)) (hT : gT ∈ blockTri (blk2 r)) {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero r y) :
    (topL r ((gT⁻¹).val * y * gS.val)).det =
      ((Matrix.GeneralLinearGroup.det (upperLeftBlock hb gT))⁻¹ * Matrix.GeneralLinearGroup.det (upperLeftBlock ha gS) : κˣ) *
        (topL r y).det := by
  have hTi : gT⁻¹ ∈ blockTri (blk2 r) := inv_mem hT
  have hinv : upperLeftBlock hb gT⁻¹ = (upperLeftBlock hb gT)⁻¹ := extendOne_inv (blkR hb) hT
  rw [topL_mul ha hb ha ((gT⁻¹).val * y) (lowZero_of_mem hS), topL_mul ha hb hb (gT⁻¹).val hy,
    Matrix.det_mul, Matrix.det_mul, topL_eq ha ha gS.val, topL_eq hb hb (gT⁻¹).val, ← upper_block_val_submatrix ha hS,
    ← upper_block_val_submatrix hb hTi, hinv, ← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply,
    map_inv, Units.val_mul]
  ring

theorem lowZero_iff {a b r : ℕ} {gS : GL (Fin a) κ} {gT : GL (Fin b) κ}
    (hS : gS ∈ blockTri (blk2 r)) (hT : gT ∈ blockTri (blk2 r)) (y : Matrix (Fin b) (Fin a) κ) :
    LowZero r ((gT⁻¹).val * y * gS.val) ↔ LowZero r y := by
  have hS' := lowZero_of_mem hS
  have hTi := lowZero_of_mem (inv_mem hT)
  constructor
  · intro h
    have hy : y = gT.val * ((gT⁻¹).val * y * gS.val) * (gS⁻¹).val := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [hy]
    exact lowZero_mul (lowZero_mul (lowZero_of_mem hT) h) (lowZero_of_mem (inv_mem hS))
  · intro h
    exact lowZero_mul (lowZero_mul hTi h) hS'

end Fin

theorem omegaQ_blockTri : ∀ (D : D7) (a b r : ℕ), r ≤ a → r ≤ b → ∀ (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ) (gS : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (gT : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), (∀ PP ∈ Q, gS PP ∈ blockTri (blk2 r)) → (∀ PP ∈ Q, gT PP ∈ blockTri (blk2 r)) → (∀ PP ∈ Q, y' PP = ((gT PP)⁻¹).val * y PP * (gS PP).val) → (∏ PP ∈ Q, (((ξ PP (Matrix.GeneralLinearGroup.det (gS PP)) : ℂˣ) : ℂ)⁻¹ * ((ξ PP (Matrix.GeneralLinearGroup.det (gT PP)) : ℂˣ) : ℂ))) ^ k * omegaQ Q r ξ k y' = (∏ PP ∈ Q, (((ξ PP (dBlk (blk2 r) 1 (gS PP)) : ℂˣ) : ℂ)⁻¹ * ((ξ PP (dBlk (blk2 r) 1 (gT PP)) : ℂˣ) : ℂ))) ^ k * omegaQ Q r ξ k y := by
  intro D a b r ha hb Q ξ k gS gT y y' hS hT hy'
  have hdet : ∀ PP ∈ Q, LowZero r (y PP) → (topL r (y' PP)).det =
      (((Matrix.GeneralLinearGroup.det (upperLeftBlock hb (gT PP)))⁻¹ * Matrix.GeneralLinearGroup.det (upperLeftBlock ha (gS PP)) :
        (kP PP)ˣ) : kP PP) * (topL r (y PP)).det := fun PP hPP hl => by
    rw [hy' PP hPP]
    exact det_topL ha hb (hS PP hPP) (hT PP hPP) hl
  have hcond : (∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det) ↔
      (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) := by
    refine forall₂_congr fun PP hPP => ?_
    have hlz : LowZero r (y' PP) ↔ LowZero r (y PP) := by
      rw [hy' PP hPP]
      exact lowZero_iff (hS PP hPP) (hT PP hPP) (y PP)
    rw [hlz]
    refine and_congr_right fun hl => ?_
    rw [hdet PP hPP hl, Units.isUnit_units_mul]
  have hsplit : ∀ (A : Pl D.host.E → ℂ) (U : Q → ℂ),
      (∏ PP ∈ Q, A PP) ^ k * ∏ PP ∈ Q.attach, U PP ^ k = ∏ PP ∈ Q.attach, (A PP.1 * U PP) ^ k := by
    intro A U
    rw [← Finset.prod_attach Q A, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    simp only [mul_zpow]
  unfold omegaQ
  by_cases h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
  · have h' := hcond.mpr h
    rw [dite_eq_left h', dite_eq_left h, hsplit, hsplit]
    refine Finset.prod_congr rfl fun PP _ => ?_
    congr 1
    obtain ⟨P, hP⟩ := PP
    have eS := det_eq ha (hS P hP)
    have eT := det_eq hb (hT P hP)
    have eU : (h' P hP).2.unit = ((Matrix.GeneralLinearGroup.det (upperLeftBlock hb (gT P)))⁻¹ *
        Matrix.GeneralLinearGroup.det (upperLeftBlock ha (gS P))) * (h P hP).2.unit := by
      ext
      rw [IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec]
      exact hdet P hP (h P hP).1
    simp only []
    rw [eS, eT, eU]
    simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  · have h' : ¬ ∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det := fun h'' => h (hcond.mp h'')
    rw [dite_eq_right h', dite_eq_right h, mul_zero, mul_zero]

end GlobalTheory.OmegaTwistLaw

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRed

section General

variable {R k : Type} [CommRing R] [CommRing k] {b a : ℕ}


open Classical in
theorem int_mul (O : Subring R) (ρ : O →+* k) (z : Matrix (Fin b) (Fin b) O) (y : Matrix (Fin a) (Fin a) O)
    (N : Matrix (Fin b) (Fin a) R) (h : ∀ i j, N i j ∈ O) :
    (∀ i j, (z.map O.subtype * N * y.map O.subtype) i j ∈ O) ∧
    (Matrix.of fun i j => if h : (z.map O.subtype * N * y.map O.subtype) i j ∈ O then
        ρ ⟨(z.map O.subtype * N * y.map O.subtype) i j, h⟩ else 0) =
      z.map ρ * (Matrix.of fun i j => if h : N i j ∈ O then ρ ⟨N i j, h⟩ else 0) * y.map ρ := by
  obtain ⟨M, rfl⟩ : ∃ M : Matrix (Fin b) (Fin a) O, N = M.map O.subtype :=
    ⟨Matrix.of fun i j => ⟨N i j, h i j⟩, by ext i j; rfl⟩
  have key : z.map O.subtype * M.map O.subtype * y.map O.subtype = (z * M * y).map O.subtype := by
    rw [Matrix.map_mul, Matrix.map_mul]
  have mem : ∀ i j, (z.map O.subtype * M.map O.subtype * y.map O.subtype) i j ∈ O := fun i j => by
    rw [key]; exact ((z * M * y) i j).2
  refine ⟨mem, ?_⟩
  have lhs : (Matrix.of fun i j => if h : (z.map O.subtype * M.map O.subtype * y.map O.subtype) i j ∈ O then
      ρ ⟨(z.map O.subtype * M.map O.subtype * y.map O.subtype) i j, h⟩ else 0) = (z * M * y).map ρ := by
    ext i j
    rw [Matrix.of_apply, dite_eq_left (mem i j), Matrix.map_apply]
    congr 1
    exact Subtype.ext (congrFun (congrFun key i) j)
  have mid : (Matrix.of fun i j => if h : M.map O.subtype i j ∈ O then ρ ⟨M.map O.subtype i j, h⟩ else 0) = M.map ρ := by
    ext i j
    rw [Matrix.of_apply, dite_eq_left (h i j)]
    rfl
  rw [lhs, mid, Matrix.map_mul, Matrix.map_mul]

theorem cancel (Z : GL (Fin b) R) (Y : GL (Fin a) R) (N : Matrix (Fin b) (Fin a) R) :
    Z.val * ((Z⁻¹).val * N * Y.val) * (Y⁻¹).val = N := by
  calc Z.val * ((Z⁻¹).val * N * Y.val) * (Y⁻¹).val
      = (Z.val * (Z⁻¹).val) * N * (Y.val * (Y⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = N := by rw [Units.mul_inv, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]

theorem move {A : Type} [CommRing A] (f : A →+* R) (βS G Y : GL (Fin a) R) (βT H Z : GL (Fin b) R)
    (hY : βS * Y * βS⁻¹ = G) (hZ : βT * Z * βT⁻¹ = H)
    (g : Matrix (Fin a) (Fin a) A) (h : Matrix (Fin b) (Fin b) A) (hg : g.map f = G.val) (hh : h.map f = (H⁻¹).val)
    (x : Matrix (Fin b) (Fin a) A) :
    (βT⁻¹).val * (h * x * g).map f * βS.val = (Z⁻¹).val * ((βT⁻¹).val * x.map f * βS.val) * Y.val := by
  have eH : (H⁻¹).val = βT.val * ((Z⁻¹).val * (βT⁻¹).val) := by
    rw [← hZ, mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
  have eG : G.val = βS.val * (Y.val * (βS⁻¹).val) := by
    rw [← hY, Units.val_mul, Units.val_mul, Matrix.mul_assoc]
  rw [Matrix.map_mul, Matrix.map_mul, hg, hh, eH, eG]
  simp only [Matrix.mul_assoc]
  rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc (βT⁻¹).val βT.val, Units.inv_mul, Matrix.one_mul]

private theorem bc_mul_restrict_mul_bc_eq (O : Subring R) (ρ : O →+* k) (z : GL (Fin b) O) (y : GL (Fin a) O)
    (N : Matrix (Fin b) (Fin a) R) (h : ∀ i j, N i j ∈ O) :
    (∀ i j, ((Formalism.UG.bc O.subtype z).val * N * (Formalism.UG.bc O.subtype y).val) i j ∈ O) ∧
    (Matrix.of fun i j => @dite _ (((Formalism.UG.bc O.subtype z).val * N * (Formalism.UG.bc O.subtype y).val) i j ∈ O)
        (Classical.propDecidable _) (fun h => ρ ⟨_, h⟩) (fun _ => 0)) =
      (Formalism.UG.bc ρ z).val *
        (Matrix.of fun i j => @dite _ (N i j ∈ O) (Classical.propDecidable _) (fun h => ρ ⟨N i j, h⟩) (fun _ => 0)) *
        (Formalism.UG.bc ρ y).val := by
  have ez : (Formalism.UG.bc O.subtype z).val = z.val.map O.subtype := rfl
  have ey : (Formalism.UG.bc O.subtype y).val = y.val.map O.subtype := rfl
  have ez' : (Formalism.UG.bc ρ z).val = z.val.map ρ := rfl
  have ey' : (Formalism.UG.bc ρ y).val = y.val.map ρ := rfl
  rw [ez, ey, ez', ey']
  exact GlobalTheory.FrameRed.int_mul O ρ z.val y.val N h

end General

variable {D : D7}

theorem isIntM_mul {b a : ℕ} (z : GL (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (y : GL (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) {N : Matrix (Fin b) (Fin a) (Datum.EAf D)}
    (h : IsIntM (D := D) N) :
    IsIntM (D := D) ((intGL D.host.F D.host.E b z).val * N * (intGL D.host.F D.host.E a y).val) ∧
    ∀ PP, redM (D := D) PP ((intGL D.host.F D.host.E b z).val * N * (intGL D.host.F D.host.E a y).val) =
      (Formalism.UG.bc (resS D.host.F PP) z).val * redM (D := D) PP N * (Formalism.UG.bc (resS D.host.F PP) y).val := by
  exact ⟨(bc_mul_restrict_mul_bc_eq _ (RingHom.id _) z y N h).1, fun PP => (bc_mul_restrict_mul_bc_eq _ (resS D.host.F PP) z y N h).2⟩

theorem mt_map (V : HSp D) (g : GA D V) :
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (finE V g).val := rfl

theorem frMapO_actO {S T : HSp D} {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    {g : GA D S} {h : GA D T} {y : GL (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    {z : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hy : frGL βS y = finE S g) (hz : frGL βT z = finE T h) (x : WO S T) :
    frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x) =
      ((intGL D.host.F D.host.E _ z)⁻¹).val * frMapO S T βS βT x * (intGL D.host.F D.host.E _ y).val := by
  have hY : βS * intGL D.host.F D.host.E _ y * βS⁻¹ = finE S g := by rw [← hy]; rfl
  have hZ : βT * intGL D.host.F D.host.E _ z * βT⁻¹ = finE T h := by rw [← hz]; rfl
  have hg : (Formalism.L2.Theta.mt S g⁻¹⁻¹).map (toEAf D) = (finE S g).val := by rw [inv_inv]; exact GlobalTheory.FrameRed.mt_map S g
  have hh : (Formalism.L2.Theta.mt T h⁻¹).map (toEAf D) = ((finE T h)⁻¹).val := by rw [GlobalTheory.FrameRed.mt_map, map_inv]
  show (βT⁻¹).val * (Formalism.L2.Theta.mt T h⁻¹ * x * Formalism.L2.Theta.mt S g⁻¹⁻¹).map (toEAf D) * βS.val = _
  exact GlobalTheory.FrameRed.move (toEAf D) βS (finE S g) (intGL D.host.F D.host.E _ y) βT (finE T h)
    (intGL D.host.F D.host.E _ z) hY hZ _ _ hg hh x

theorem isIntM_iff {b a : ℕ} (z : GL (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (y : GL (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (N : Matrix (Fin b) (Fin a) (Datum.EAf D)) :
    IsIntM (D := D) (((intGL D.host.F D.host.E b z)⁻¹).val * N * (intGL D.host.F D.host.E a y).val) ↔
      IsIntM (D := D) N := by
  constructor
  · intro hM
    have h1 := (GlobalTheory.FrameRed.isIntM_mul (D := D) z y⁻¹ hM).1
    rwa [map_inv (intGL D.host.F D.host.E a) y, GlobalTheory.FrameRed.cancel] at h1
  · intro hN
    have h1 := (GlobalTheory.FrameRed.isIntM_mul (D := D) z⁻¹ y hN).1
    rwa [map_inv (intGL D.host.F D.host.E b) z] at h1

theorem redM_mul {b a : ℕ} (z : GL (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (y : GL (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) {N : Matrix (Fin b) (Fin a) (Datum.EAf D)}
    (h : IsIntM (D := D) N) (PP : Pl D.host.E) :
    redM (D := D) PP (((intGL D.host.F D.host.E b z)⁻¹).val * N * (intGL D.host.F D.host.E a y).val) =
      ((Formalism.UG.bc (resS D.host.F PP) z)⁻¹).val * redM (D := D) PP N * (Formalism.UG.bc (resS D.host.F PP) y).val := by
  have h1 := (GlobalTheory.FrameRed.isIntM_mul (D := D) z⁻¹ y h).2 PP
  rwa [map_inv (intGL D.host.F D.host.E b) z, map_inv (Formalism.UG.bc (resS D.host.F PP)) z] at h1

theorem frMapO_actO_red : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ x : WO S T, (IsIntM (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) ↔ IsIntM (frMapO S T βS βT x)) ∧ (IsIntM (frMapO S T βS βT x) → ∀ PP, redM PP (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) = ((redFn βT PP (finE T h))⁻¹).val * redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S g)).val) := by
  intro D S T βS βT g h hg hh x
  unfold St at hg hh
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hg
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 hh
  have e := GlobalTheory.FrameRed.frMapO_actO hy hz x
  refine ⟨?_, fun hI PP => ?_⟩
  · rw [e]
    exact GlobalTheory.FrameRed.isIntM_iff z y _
  · rw [e, GlobalTheory.FrameRed.redM_mul z y hI PP]
    have a : redFn βS PP (finE S g) = Formalism.UG.bc (resS D.host.F PP) y := by
      rw [← hy]; exact redFn_frGL βS PP y
    have b : redFn βT PP (finE T h) = Formalism.UG.bc (resS D.host.F PP) z := by
      rw [← hz]; exact redFn_frGL βT PP z
    rw [a, b]

end GlobalTheory.FrameRed

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  first | exact @GlobalTheory.StabLatInv.mem_latO_iff_actO_mem | exact GlobalTheory.StabLatInv.mem_latO_iff_actO_mem | (intros; apply GlobalTheory.StabLatInv.mem_latO_iff_actO_mem <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

theorem div_or_isConjPl_div : ∀ (D : D7) (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → P.Div k PP ∨ ∃ PP', P.Div k PP' ∧ Formalism.IndefR.Lev.IsConjPl PP' PP := by
  intro D P k PP h
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D P k PP h with h1 | ⟨w, h1, h2⟩
  · exact Or.inl h1
  · refine Or.inr ⟨w, h1, fun c hc => ⟨Formalism.L2.Col.cO D.host.E c, ?_, rfl⟩⟩
    rw [h2, Formalism.L2.Col.conjIdeal_eq] at hc
    exact hc

end GlobalTheory.StepLaw
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.no_intertwiner_smaller_fock_to_discrete_series : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFifth X := by
  first | exact @GlobalTheory.SmallerSource.no_map_smaller_source | exact GlobalTheory.SmallerSource.no_map_smaller_source | (intros; apply GlobalTheory.SmallerSource.no_map_smaller_source <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.discreteSeries_integrableCoefficient_projector : ∀ X : ProvA, DiscreteSeriesPositivity X → CoverHaarIntegration X → DiscreteSeriesHighestVector X := by
  first | exact @GlobalTheory.DSProj.discreteSeriesHighestVector_of_positivity | exact GlobalTheory.DSProj.discreteSeriesHighestVector_of_positivity | (intros; apply GlobalTheory.DSProj.discreteSeriesHighestVector_of_positivity <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.theta_correspondence_fock_ds_uniqueness : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → admQ7 → admQ8 → ArchimedeanRallisFirst X → ArchimedeanRallisSecond X → ArchimedeanRallisUpDownLine X := by
  first | exact @GlobalTheory.ThetaUnique.theta_unique | exact GlobalTheory.ThetaUnique.theta_unique | (intros; apply GlobalTheory.ThetaUnique.theta_unique <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

theorem _root_.GlobalTheory.T.continuous_characters_locallyConstant_nonarchLocalField : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ μ : kˣ →* ℂˣ, Continuous μ → IsOpen (μ.ker : Set kˣ)) ∧ ∀ ψ : AddChar k Circle, Continuous ψ → IsLocallyConstant (fun x : k => (ψ x : ℂ)) := by
  first | exact @GlobalTheory.RootEx.OpenKernel.characters_locallyConstant | exact GlobalTheory.RootEx.OpenKernel.characters_locallyConstant | (intros; apply GlobalTheory.RootEx.OpenKernel.characters_locallyConstant <;> assumption)
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.exists_piTensor_tmul_piTensor_linearEquiv_piTensor_tmul : ∀ (ι : Type) [Fintype ι] (F V : ι → Type) [∀ τ, AddCommGroup (F τ)] [∀ τ, Module ℂ (F τ)] [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)], ∃ e : ((⨂[ℂ] τ, F τ) ⊗[ℂ] (⨂[ℂ] τ, V τ)) ≃ₗ[ℂ] (⨂[ℂ] τ, (F τ ⊗[ℂ] V τ)), ∀ (f : ∀ τ, F τ) (v : ∀ τ, V τ), e (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (fun τ => f τ ⊗ₜ[ℂ] v τ) := by
  first | exact @GlobalTheory.exists_piTensor_shuffle_equiv | exact GlobalTheory.exists_piTensor_shuffle_equiv | (intros; apply GlobalTheory.exists_piTensor_shuffle_equiv <;> assumption)
end
