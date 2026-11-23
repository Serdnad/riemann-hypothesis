module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle038
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle037
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle049
public import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import GroundTheory.AutomorphicForms.GL2.GJMatrixCoord
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle063
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle060
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle026
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.IntegralCovGen
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle053
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BlockDiagonalPreservesFormIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle035
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.ExistsGlCol
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.Bundle001
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MemStabiliserIffFrameLowerBlock
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.FrameInvPf
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle058
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle048
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.IncMFromBlocks

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
theorem surj_k {γ : d.G} (hγ : γ ∈ rat2 σ d.Y) (hS : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ ∃ g ∈ rat2 σ L.Y, γ = p * L.j g := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  subst hee
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) γ hγ
  obtain ⟨G0', hG0'⟩ := Afc.rat_frame (b := d.b) γ⁻¹ (inv_mem hγ)
  have hGG : G0' * G0 = 1 := kfour.incM_injective (F := F) (by
    rw [kfour.incM_mul', ← hG0, ← hG0', ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one,
      Afc.incM_one'])
  have hS0 : ∀ i, G0 (Sum.inr i) (Sum.inl L.i₀) = 0 := fun i => by
    have h1 := hS i
    rw [hG0] at h1
    exact kfour.inclR_injective (F := F) (h1.trans (map_zero _).symm)
  set v : Fin d.n → E := fun k => G0 (Sum.inl k) (Sum.inl L.i₀) with hv_def
  have hv : v ≠ 0 := by
    intro h0
    have h1 := congrFun (congrFun hGG (Sum.inl L.i₀)) (Sum.inl L.i₀)
    have h2 : ∀ k, G0 (Sum.inl k) (Sum.inl L.i₀) = 0 := fun k => congrFun h0 k
    rw [Matrix.mul_apply, Fintype.sum_sum_type] at h1
    simp only [h2, hS0, mul_zero, Finset.sum_const_zero, add_zero, Matrix.one_apply_eq] at h1
    exact zero_ne_one h1
  obtain ⟨a, ha⟩ := exists_gl_col L.i₀ v hv
  obtain ⟨p1, hp1r, hp1⟩ := Afc.levi_ex hσ d.ok.frame a⁻¹
  have hp1P : p1 ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame p1).2 (by rw [hp1, Matrix.toBlocks_fromBlocks₂₁])
  set P1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
    Matrix.fromBlocks (a⁻¹).1 0 0 ((((a⁻¹)⁻¹).1)ᵀ.map σ) with hP1_def
  have hP1 : inFrame d.b p1 = incM F P1 := by
    rw [hp1, hP1_def, Afc.incM_fromBlocks, show incM F (0 : Matrix (Fin d.n) (Fin d.n) E) = 0 from kfour.incM_zero]
  set M1 := P1 * G0 with hM1_def
  have hM1 : inFrame d.b (p1 * γ) = incM F M1 := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hP1, hG0, hM1_def, kfour.incM_mul']
  have hγ1 : p1 * γ ∈ rat2 σ d.Y := mul_mem hp1r hγ
  have hx : ∀ r, M1 r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀) := by
    intro r
    rw [hM1_def, Matrix.mul_apply, Fintype.sum_sum_type]
    rcases r with i | i
    · simp only [hP1_def, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul,
        Finset.sum_const_zero, add_zero]
      have e1 : ∀ j, G0 (Sum.inl j) (Sum.inl L.i₀) = a.1 j L.i₀ := fun j => (ha j).symm
      simp only [e1]
      rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      simp [Matrix.one_apply]
    · simp [hP1_def, hS0, Matrix.one_apply]
  have hform := form_E hε (p1 * γ) hM1
  have hy := yrow_zero hform hx
  set H := M1.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) with hH_def
  have hH := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.blockH_form_k L hform hx hy
  have hε1 : (((ε : ℤ) : E)) * (((ε : ℤ) : E)) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hεσ : (σ : E →+* E) (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast _ _
  obtain ⟨hHH', hH'H⟩ := kunf.frame_inv_pf (σ : E →+* E) hσ (((ε : ℤ) : E)) hε1 hεσ H hH
  set H' := Matrix.fromBlocks ((H.toBlocks₂₂.map (σ : E →+* E))ᵀ) ((((ε : ℤ) : E)) • (H.toBlocks₁₂.map (σ : E →+* E))ᵀ)
      ((((ε : ℤ) : E)) • (H.toBlocks₂₁.map (σ : E →+* E))ᵀ) ((H.toBlocks₁₁.map (σ : E →+* E))ᵀ) with hH'_def
  have hIA : incM F H * incM F H' = 1 := by rw [← kfour.incM_mul', hHH', Afc.incM_one']
  have hformA : (incM F H)ᵀ * kunf.jw L.n (((ε : ℤ) : AE F E)) * (incM F H).map (cA σ) =
      kunf.jw L.n (((ε : ℤ) : AE F E)) := by
    have h1 := congrArg (incM F) hH
    rw [kfour.incM_mul', kfour.incM_mul', ← Afc.incM_transpose, ← Afc.incM_map_cA, ← QA_eq] at h1
    exact h1
  obtain ⟨h, hh⟩ := kunf.exists_of_frame (Y := L.Y) hε' (incM F H) (incM F H') hIA hformA
  have hhr : h ∈ rat2 σ L.Y := kunf.rat_of_inFrame hh
  have hh' : inFrame L.b h⁻¹ = incM F H' := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hh]
    exact Matrix.inv_eq_right_inv hIA
  have hnF : inFrame d.b (p1 * γ * L.j h⁻¹) = incM F (M1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hP1, hG0, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k, hh', _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_incM_k, hM1_def,
      kfour.incM_mul', kfour.incM_mul']
  have hnq : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b (p1 * γ * L.j h⁻¹)) := by
    rw [hnF]
    exact NQ.map _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.nq_E_k L hx hy hHH')
  have hnP : p1 * γ * L.j h⁻¹ ∈ par2 σ d.Y := (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame _).2 hnq.projected_block_lower_sum
  have hnR : p1 * γ * L.j h⁻¹ ∈ rat2 σ d.Y := mul_mem hγ1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L (inv_mem hhr))
  refine ⟨p1⁻¹ * (p1 * γ * L.j h⁻¹), mul_mem (inv_mem hp1P) hnP, mul_mem (inv_mem hp1r) hnR, h, hhr, ?_⟩
  rw [map_inv]
  group
theorem rep_mk_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (x : rat2 σ d.Y) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) x) = p * x := by
  obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1
    (Quotient.out_eq (GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) x)).symm
  refine ⟨((γ : rat2 σ d.Y) : d.G), Subgroup.mem_subgroupOf.1 γ.2, (γ : rat2 σ d.Y).2, ?_⟩
  show (((Quotient.out (GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) x)) : rat2 σ d.Y) : d.G) = _
  rw [← hγ]
  rfl
end Bq
theorem cos_bij_pf_k : ∃ e : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd ≃ {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ∀ q', ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
    _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1 = p * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') := by
  set H := (par2 σ d.Y).subgroupOf (rat2 σ d.Y) with hH
  set H' := (par2 σ L.Y).subgroupOf (rat2 σ L.Y) with hH'
  let jr : rat2 σ L.Y → rat2 σ d.Y := fun γ => ⟨L.j γ, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L γ.2⟩
  let e0 : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd → _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d := Quotient.lift (fun γ => GlobalTheory.AutomorphicL2Unitary.mk H (jr γ)) (by
    intro a b hab
    have hab' : b * a⁻¹ ∈ H' := QuotientGroup.rightRel_apply.1 hab
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    refine ⟨⟨jr (b * a⁻¹), ?_⟩, ?_⟩
    · rw [hH', Subgroup.mem_subgroupOf] at hab'
      rw [hH, Subgroup.mem_subgroupOf]
      exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_par_k L hab'
    · apply Subtype.ext
      show L.j ((b : G2 σ L.Y) * (a : G2 σ L.Y)⁻¹) * L.j a = L.j b
      rw [map_mul, map_inv, inv_mul_cancel_right])
  have he0 : ∀ γ, e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ) = GlobalTheory.AutomorphicL2Unitary.mk H (jr γ) := fun γ => rfl
  have hS : ∀ q', _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 q')) := by
    intro q'
    induction q' using Quotient.inductionOn with
    | h γ =>
      obtain ⟨p, hp, -, hrep⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.rep_mk_k (jr γ)
      have e1 : _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ)) = p * L.j γ := by rw [he0]; exact hrep
      show _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ)))
      rw [e1]
      exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.inStabilizer_parabolic_mul L hp (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.inStabilizer_smallerGroupEmbed L γ)
  let e : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd → {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)} := fun q' => ⟨e0 q', hS q'⟩
  have hinj : Function.Injective e := by
    intro q1 q2 h12
    have h0 : e0 q1 = e0 q2 := congrArg Subtype.val h12
    induction q1 using Quotient.inductionOn with
    | h a =>
      induction q2 using Quotient.inductionOn with
      | h b =>
        change GlobalTheory.AutomorphicL2Unitary.mk H (jr a) = GlobalTheory.AutomorphicL2Unitary.mk H (jr b) at h0
        obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h0
        have hγv : ((γ : rat2 σ d.Y) : d.G) = L.j ((b : G2 σ L.Y) * (a : G2 σ L.Y)⁻¹) := by
          have := congrArg Subtype.val hγ
          simp only [Subgroup.coe_mul, jr] at this
          rw [map_mul, map_inv, ← this, mul_inv_cancel_right]
        have hP : (b : G2 σ L.Y) * (a : G2 σ L.Y)⁻¹ ∈ par2 σ L.Y := by
          apply _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.par_of_j_k L
          rw [← hγv]
          exact Subgroup.mem_subgroupOf.1 γ.2
        change GlobalTheory.AutomorphicL2Unitary.mk H' a = GlobalTheory.AutomorphicL2Unitary.mk H' b
        rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
        refine ⟨⟨b * a⁻¹, Subgroup.mem_subgroupOf.2 hP⟩, ?_⟩
        simp
  have hsurj : Function.Surjective e := by
    rintro ⟨q, hq⟩
    obtain ⟨p, hpP, hpR, g, hg, hγ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.surj_k L (Quotient.out q).2 hq
    refine ⟨GlobalTheory.AutomorphicL2Unitary.mk H' ⟨g, hg⟩, Subtype.ext ?_⟩
    show GlobalTheory.AutomorphicL2Unitary.mk H (jr ⟨g, hg⟩) = q
    conv_rhs => rw [← Quotient.out_eq q]
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    refine ⟨⟨⟨p, hpR⟩, Subgroup.mem_subgroupOf.2 hpP⟩, Subtype.ext ?_⟩
    exact hγ.symm
  refine ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, fun q' => ?_⟩
  induction q' using Quotient.inductionOn with
  | h γ =>
    obtain ⟨p, hpP, hpR, hrep⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.rep_mk_k (jr γ)
    obtain ⟨p', hp'P, hp'R, hrep'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.rep_mk_k (d := L.sd) γ
    refine ⟨p * L.j p'⁻¹, mul_mem hpP (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_par_k L (inv_mem hp'P)), mul_mem hpR (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L (inv_mem hp'R)), ?_⟩
    show _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ)) = _
    rw [he0, hrep, hrep', map_mul, map_inv]
    simp only [jr]
    group
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
set_option linter.style.haveILetI false
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.Twp
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem ratM_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Mx F E d.m d.n) :
    X ∈ d.ratM ↔ d.crd X ∈ GroundTheory.Automorphic.FourierWhittaker.vecLattice F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) := by
  let c : Mx F E d.m d.n →+ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F) :=
    { toFun := d.crd, map_zero' := by funext k; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd], map_add' := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_add d }
  constructor
  · intro hX
    have hle : d.ratM ≤ (GroundTheory.Automorphic.FourierWhittaker.vecLattice F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d)).comap c := by
      refine (AddSubgroup.closure_le _).mpr ?_
      rintro _ ⟨M, rfl⟩
      refine ⟨fun k => d.bs.repr (M k.1 k.2.1) k.2.2, ?_⟩
      funext k
      exact (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM d M k).symm
    exact hle hX
  · rintro ⟨ξ, hξ⟩
    let M : Matrix (Fin d.m) (Fin d.n) E := Matrix.of fun i j => ∑ k, ξ (i, j, k) • d.bs k
    have e1 : d.crd (incM F M) = d.crd X := by
      funext k
      rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM d _ k]
      have h2 := congrFun hξ k
      simp only [AddMonoidHom.compLeft, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply] at h2
      rw [← h2]
      show _ = algebraMap F (AF F) (ξ k)
      congr 1
      exact congrFun (d.bs.repr_sum_self fun k' => ξ (k.1, k.2.1, k')) k.2.2
    have e2 : incM F M = X := by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d (incM F _), e1, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd]
    rw [← e2]
    exact AddSubgroup.subset_closure ⟨_, rfl⟩
theorem integral_cov_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ν : Measure (Mx F E d.m d.n)) (hν : d.IsCov ν) (h : Mx F E d.m d.n → ℂ) :
    ∫ Z, h Z ∂ν = ∫ c, h (d.cmb c) ∂(GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d)) := by
  obtain ⟨hT, hLC, hSC, hB, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.meas_mx_top'_k d
  haveI := hT; haveI := hLC; haveI := hSC; haveI := hB; haveI := hC
  obtain ⟨hH, 𝓕, h𝓕, h1⟩ := hν
  haveI := hH
  exact integral_cov_gen (hBor := hB) (hνH := hH) d.ratM (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cEquiv_k d (Equiv.refl (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d))) (fun X => _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.ratM_iff_k d X) ν 𝓕 h𝓕 h1 h
end PositivityTheory.SiegelWeilFormula.TW.Twp
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
def cMF_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (δ : E) (c : (Fin L.n → AE F E) × AF F) :
    Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2) 0 ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ.map (cA σ))
def cMF'_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (δ : E) (c : (Fin L.n → AE F E) × AF F) :
    Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1)) (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ.map (cA σ))) 0 ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ.map (cA σ))
theorem cMF_mul_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (δ : E) (c : (Fin L.n → AE F E) × AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_k (σ := σ) L δ c * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF'_k L δ c = 1 := by
  have e1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k L c.1
  have e2 : (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ.map (cA σ) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ.map (cA σ) = 1 := by
    rw [← kunf.map_cA_mul, ← Matrix.transpose_mul, e1, Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have e3 : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1 * -(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ.map (cA σ)) +
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ.map (cA σ) = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, neg_add_cancel]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF'_k, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [e1, e2, e3, Matrix.fromBlocks_one]
theorem continuous_aB_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (δ : E) :
    Continuous fun c : (Fin L.n → AE F E) × AF F => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k (σ := σ) L δ c.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single_apply]
  split_ifs
  · exact Continuous.smul (continuous_snd (X := Fin L.n → AE F E) (Y := AF F))
      (continuous_const (y := inclR (F := F) (E := E) (AF F) δ))
  · exact continuous_const
theorem continuous_cM_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) : Continuous cM := by
  have hF : ∀ c, inFrame d.b (cM c) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_k L δ c := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h
  have hN := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_unipotent_nilpotent L
  have hU : Continuous fun c : (Fin L.n → AE F E) × AF F => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1 :=
    continuous_const.add (hN.comp continuous_fst)
  have hUn : Continuous fun c : (Fin L.n → AE F E) × AF F => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1) :=
    continuous_const.add (hN.comp continuous_fst.neg)
  have hcA : Continuous fun M : Matrix (Fin d.n) (Fin d.n) (AE F E) => M.map (cA σ) :=
    continuous_id.matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)
  have hA := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_aB_k (σ := σ) L δ
  have hc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_k (σ := σ) L δ) :=
    Continuous.matrix_fromBlocks hU hA continuous_const (hcA.comp hUn.matrix_transpose)
  have hc' : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF'_k (σ := σ) L δ) :=
    Continuous.matrix_fromBlocks hUn ((hUn.matrix_mul hA).matrix_mul (hcA.comp hU.matrix_transpose)).neg
      continuous_const (hcA.comp hU.matrix_transpose)
  have h1 : Continuous fun c => incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_k L δ c * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  have h2 : Continuous fun c => incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF'_k L δ c * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc').matrix_mul continuous_const
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine h1.congr fun c => ?_
    show _ = mat2 (cM c)
    rw [kunf.matrix_eq_inFrame_conj d.b, hF c]
  · refine h2.congr fun c => ?_
    show _ = mat2 (cM c)⁻¹
    rw [kunf.matrix_eq_inFrame_conj d.b, GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hF c, Matrix.inv_eq_right_inv (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_mul_k L δ c)]
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def rot_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) : d.G :=
  (((Finset.univ : Finset (InfinitePlace F)).toList).map fun w => R.ι w (yrot d.n (R.sg w) t)).prod
theorem rot_mem_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) : _root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k R t ∈ d.K := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k
  refine d.K.list_prod_mem fun x hx => ?_
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.iota_mem_K_k d R w _ (by rw [mR_yrot]; exact inK_yrotM _ _ _)
theorem exists_tw_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) :
    ∃ W' : Mx F E d.m d.n, finOne F • W' = 0 ∧ ∀ w, d.cw w W' = (-(((R.sg w : ℤ) : ℂ) * R.ζ)) • d.cw w W := by
  obtain ⟨s, -, hs1, hs2, -, -⟩ := Place.exists_sec d.cm d.B.emb
  refine ⟨s (fun w => -(((R.sg w : ℤ) : ℂ) * R.ζ)) • W, ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    rw [← smul_mul_assoc, hs2, zero_mul]
  · ext i j
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hs1]
def tw_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) : Mx F E d.m d.n := (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_tw_k R W).choose
def vline_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (W : Mx F E d.m d.n) (z : ℂ) : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  (realAd F z.re • W) * (incM F d.b.1.toCols₂)ᵀ + (realAd F z.im • _root_.PositivityTheory.SiegelWeilFormula.KFP.tw_k R W) * (incM F d.b.1.toCols₁)ᵀ
theorem fin_eq_zero_iff_k (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X = 0 ↔ finOne F • X = 0 := by
  set bas := Algebra.TensorProduct.basis (AF F) d.bs
  have key : ∀ z : AE F E, finOne F • z = 0 ↔ ∀ l, (bas.repr z l).2 = 0 := by
    intro z
    rw [← bas.repr.injective.eq_iff, LinearEquiv.map_smul, LinearEquiv.map_zero]
    simp only [Finsupp.ext_iff, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply,
      finOne_mul_eq_zero_iff]
  constructor
  · intro h
    ext i j
    simp only [Matrix.smul_apply, Matrix.zero_apply]
    refine (key _).2 fun l => ?_
    exact congrFun h (i, j, l)
  · intro h
    funext ⟨i, j, l⟩
    exact (key (X i j)).1 (by simpa using congrFun (congrFun h i) j) l
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end
