module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle154
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle016
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle024
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle015
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle025
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle001
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle019
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle023
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle029

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

theorem chi_exp {χ : (AE D)ˣ →* Circle} {θ : InfFam D} (hθ : IsInfFam θ) (hχ : IsHeckeChar D χ) {m : ℕ}
    (hη : ResEta D χ m) (τ : D.what₂.Tau) :
    ∃ k : ℤ, Even (k - (m : ℤ)) ∧ ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 →
      (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
      ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ k := by
  classical
  obtain ⟨a, ha⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ χ m τ hθ hχ hη
  have ha' := ha
  obtain ⟨k, hk, hall⟩ := ha
  refine ⟨k, ?_, hall.2 θ hθ⟩
  obtain ⟨η, -, hη2, hη3, -⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  obtain ⟨k', hk', hall'⟩ := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist ha' (hη2 τ) m
  have ek : k' = k - m := by
    have : (k' : ℚ) = k - m := by rw [hk', hk]; ring
    exact_mod_cast this
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom hσ
  let w : D.what₂.Tau → ℂ := Pi.mulSingle τ (-1)
  have ww : w * w = 1 := by
    funext τ'
    simp only [w, Pi.mul_apply, Pi.one_apply, Pi.mulSingle_apply]
    split_ifs <;> simp
  let x0 : (AE D)ˣ := ⟨e w, e w, by rw [← map_mul, ww, map_one], by rw [← map_mul, ww, map_one]⟩
  have hx0 : (x0 : AE D) = e w := rfl
  have hfix : cA D (x0 : AE D) = x0 := by
    refine GlobalTheory.SplitCharExp.ext_of_chart hσ ?_ fun τ' => ?_
    · have e3 : finPart D (cA D (x0 : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x0 : AE D)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig _
      rw [e3, hx0, e1, RingHom.map_one]
    · rw [GlobalTheory.FockCompare.comp_cA hθ, hx0, e2]
      simp only [w, Pi.mulSingle_apply]
      split_ifs <;> simp
  obtain ⟨b, hb⟩ := GlobalTheory.CharConjFixed.fixed_unit D x0 hfix
  obtain ⟨⟨η0, hη0⟩, hχ0⟩ := hη
  have hξ : (χ * (η ^ m)⁻¹) x0 = 1 := by
    rw [← hb, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, hχ0 η0 hη0 b, hη3.2 η0 hη0 b, pow_one,
      mul_inv_cancel]
  have hv := hall'.2 θ hθ x0 (by rw [hx0, e1]) fun τ' h => by rw [hx0, e2]; simp [w, Pi.mulSingle_eq_of_ne h]
  rw [hξ, hx0, e2] at hv
  simp only [w, Pi.mulSingle_eq_same, norm_neg, norm_one, Complex.ofReal_one, div_one, Circle.coe_one] at hv
  rw [← ek]
  have hv' : ((-1 : ℂ)) ^ k' = 1 := by simpa using hv.symm
  rcases Int.even_or_odd k' with h | h
  · exact h
  · exfalso
    rw [h.neg_one_zpow] at hv'
    norm_num at hv'

def mOf (a : GL (Fin n) ℂ) : PositivityTheory.Rg.Sw.GR n where
  val :=
    { val := fromBlocks a.1 0 0 (a⁻¹).1ᴴ
      inv := fromBlocks (a⁻¹).1 0 0 a.1ᴴ
      val_inv := by
        rw [fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← conjTranspose_mul, Units.mul_inv,
          conjTranspose_one]
        exact fromBlocks_one
      inv_val := by
        rw [fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← conjTranspose_mul, Units.inv_mul,
          conjTranspose_one]
        exact fromBlocks_one }
  property := by
    show InG (fromBlocks a.1 0 0 (a⁻¹).1ᴴ)
    simp only [InG, JJ, fromBlocks_conjTranspose, conjTranspose_zero, conjTranspose_conjTranspose, fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
      Matrix.neg_mul, Units.inv_mul, ← conjTranspose_mul, Units.mul_inv, conjTranspose_one, neg_zero]

theorem mR_mOf (a : GL (Fin n) ℂ) : mR (mOf a) = fromBlocks a.1 0 0 (a⁻¹).1ᴴ := rfl

theorem mR_mOf_inv (a : GL (Fin n) ℂ) : mR (mOf a)⁻¹ = fromBlocks (a⁻¹).1 0 0 a.1ᴴ := rfl

theorem component_block_matrix {R : Type} (θ : InfFam D) (τ : D.what₂.Tau) (a b c d : Matrix (Fin n) (Fin n) (AE D)) :
    compAt θ τ (blk4 a b c d) = blk4 (compAt θ τ a) (compAt θ τ b) (compAt θ τ c) (compAt θ τ d) := by
  rw [compAt_eq_map, blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map]; rfl

theorem finite_part_block_matrix_map (a b c d : Matrix (Fin n) (Fin n) (AE D)) :
    (blk4 a b c d).map (finPart D) = blk4 (a.map (finPart D)) (b.map (finPart D)) (c.map (finPart D)) (d.map (finPart D)) := by
  rw [blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map]; rfl

theorem block_matrix_diagonal_one_eq_one {R : Type} [Zero R] [One R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  simp only [blk4, fromBlocks_one, submatrix_one_equiv]

theorem compAt_adj {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (X : Matrix (Fin n) (Fin n) (AE D)) :
    compAt θ τ (adj X) = (compAt θ τ X)ᴴ := by
  ext i j
  simp only [compAt, adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
  rw [GlobalTheory.FockCompare.comp_cA hθ]
  rfl

theorem finPart_adj (X : Matrix (Fin n) (Fin n) (AE D)) (hX : X.map (finPart D) = 1) : (adj X).map (finPart D) = 1 := by
  ext i j
  have e3 : finPart D (cA D (X j i)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (X j i)) :=
    GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig _
  have := congrFun (congrFun hX j) i
  simp only [Matrix.map_apply] at this
  simp only [adj, Matrix.map_apply, Matrix.transpose_apply, e3, this, Matrix.one_apply]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

end PositivityTheory.Rg.Sw.Glob.LocLawH
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.VacH

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC
  PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacE PositivityTheory.Rg.Sw.Glob.VacF PositivityTheory.Rg.Sw.Glob.VacG

theorem row_norm {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : u * uᴴ = 1) (x : Fin n → ℂ) :
    ∑ j, ((‖∑ k, x k * u k j‖ ^ 2 : ℝ) : ℂ) = ∑ k, ((‖x k‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    intro z
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h1]
  have hu2 : ∀ k l, ∑ j, u k j * star (u l j) = if k = l then 1 else 0 := by
    intro k l
    have h := congrFun (congrFun hu k) l
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  calc ∑ j, (∑ k, x k * u k j) * star (∑ k, x k * u k j)
      = ∑ j, ∑ k, ∑ l, x k * star (x l) * (u k j * star (u l j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [star_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [star_mul']
        ring
    _ = ∑ k, ∑ l, x k * star (x l) * ∑ j, u k j * star (u l j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ k, x k * star (x k) := by
        simp only [hu2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem levF_unitary {m n : ℕ} (e : ℤ) (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (K γ0 : ℂ) :
    levF e u (DG (m := m) (n := n) K (fun _ _ => γ0)) =
      DG (K * (u.det ^ e * (star u.det) ^ ((m : ℤ) - e))) (fun _ _ => γ0) := by
  funext v
  have hu' : u * uᴴ = 1 := mul_eq_one_comm.mp hu
  have key : ∀ a : Fin m, ∏ j : Fin n, Complex.exp (-γ0 * ((‖(Matrix.of v * u) a j‖ ^ 2 : ℝ) : ℂ))
      = ∏ j : Fin n, Complex.exp (-γ0 * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) := by
    intro a
    rw [← Complex.exp_sum, ← Complex.exp_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 2
    simpa [Matrix.mul_apply] using row_norm u hu' (v a)
  simp only [levF, DG, key]
  ring

theorem dbl_angle (ρ x : ℝ) (hρ : ρ ^ 2 = 1) :
    ((Real.cos (x / 2) : ℂ) + Complex.I * (ρ : ℂ) * (Real.sin (x / 2) : ℂ)) *
      ((Real.cos (x / 2) : ℂ) + Complex.I * (ρ : ℂ) * (Real.sin (x / 2) : ℂ)) =
    (Real.cos x : ℂ) + Complex.I * (ρ : ℂ) * (Real.sin x : ℂ) := by
  have hc := Real.cos_two_mul (x / 2)
  have hs := Real.sin_two_mul (x / 2)
  have hp := Real.sin_sq_add_cos_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hc hs
  rw [hc, hs]
  generalize Real.cos (x / 2) = c at *
  generalize Real.sin (x / 2) = s at *
  push_cast
  have hp' : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hp
  have hρ' : (ρ : ℂ) ^ 2 = 1 := by exact_mod_cast hρ
  linear_combination (-1 : ℂ) * hp' + (s : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * Complex.I_sq - (s : ℂ) ^ 2 * hρ'

end PositivityTheory.Rg.Sw.Glob.VacH
end
end
