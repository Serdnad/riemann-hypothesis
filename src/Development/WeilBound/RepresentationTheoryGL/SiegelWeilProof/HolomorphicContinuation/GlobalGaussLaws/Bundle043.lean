module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle011
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle016
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle038
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle042
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle017
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle024
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle014
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HasTemperateGrowthEvalPoly
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle041
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle021
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem gIauto_of (hT : PositivityTheory.PfSWUS.ThetaAuto) (hM : TensMem) : GIauto := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC Ψ hΨ
  have hm := hM D n V θ l s τ ε fr hC.hθ (lNZ D ψ θ l hC.hψ hC.hθ hC.hl) hC.hs hC.hfr Ψ hΨ 1
  have hphi : (phiS θ τ fr (cLoc l τ) Ψ 1).1 = tens θ τ fr (fP (cLoc l τ) 1) Ψ := by
    unfold phiS
    rw [dite_eq_left hm.1]
  have hStd : PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (phiS θ τ fr (cLoc l τ) Ψ 1) :=
    ⟨hC.hψ, hC.hχ, hC.hη, hC.hθ, hC.hμ, hC.hω, hC.hH, hC.hl, hC.hs, hC.hν, by rw [hphi]; exact hm.2⟩
  obtain ⟨h1, h2⟩ := hT D n V ψ χ θ μ ω H l s ν _ hStd hC.hr
  exact ⟨h1, fun γ hγ g => h2 γ hγ g⟩

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem thetaInt_smul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n))
    (ν : Measure (GA D V)) (Φ : schwartzA θ V.rank n) (a : ℂ) (g : G D n) :
    thetaInt ω ν (a • Φ) g = a * thetaInt ω ν Φ g := by
  have h : GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω (a • Φ) g) = fun q => a * GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g) q := by
    funext q
    simp [GlobalTheory.AutomorphicL2Unitary.descend, theta, map_smul, tsum_mul_left]
  simp only [thetaInt, h, MeasureTheory.average, MeasureTheory.integral_const_mul]

theorem tens_fP_add {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (Ψ : Mx D m n → ℂ) (P Q : PX m n) :
    tens θ τ fr (fP c (P + Q)) Ψ = tens θ τ fr (fP c P) Ψ + tens θ τ fr (fP c Q) Ψ := by
  funext x
  simp only [tens, fP, evX, map_add (f := _), Pi.add_apply]
  ring

theorem tens_fP_smul {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (Ψ : Mx D m n → ℂ) (a : ℂ) (P : PX m n) :
    tens θ τ fr (fP c (a • P)) Ψ = a • tens θ τ fr (fP c P) Ψ := by
  funext x
  simp only [tens, fP, evX, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, Pi.smul_apply, smul_eq_mul]
  ring

theorem linSec_of : ThLin → LinSec := by
  intro hTL D n V ψ χ θ μ ω H l s ν τ ε fr ι c Ψ hΨ
  have hl0 : ∀ τ, l τ ≠ 0 := lNZ D ψ θ l c.hψ c.hθ c.hl
  have hm : ∀ P, tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ schwartzA θ V.rank n ∧
      tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ fockA θ V n l s :=
    fun P => tensMem D n V θ l s τ ε fr c.hθ hl0 c.hs c.hfr Ψ hΨ P
  have hphi : ∀ P, phiS θ τ fr (cLoc l τ) Ψ P = ⟨_, (hm P).1⟩ := fun P => dif_pos (hm P).1
  have hadd : ∀ P Q, phiS θ τ fr (cLoc l τ) Ψ (P + Q) = phiS θ τ fr (cLoc l τ) Ψ P + phiS θ τ fr (cLoc l τ) Ψ Q := by
    intro P Q
    rw [hphi, hphi, hphi]
    exact Subtype.ext (tens_fP_add θ τ fr _ Ψ P Q)
  have hsmul : ∀ (a : ℂ) P, phiS θ τ fr (cLoc l τ) Ψ (a • P) = a • phiS θ τ fr (cLoc l τ) Ψ P := by
    intro a P
    rw [hphi, hphi]
    exact Subtype.ext (tens_fP_smul θ τ fr _ Ψ a P)
  have hstd : ∀ P, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (phiS θ τ fr (cLoc l τ) Ψ P) := fun P =>
    ⟨c.hψ, c.hχ, c.hη, c.hθ, c.hμ, c.hω, c.hH, c.hl, c.hs, c.hν, by rw [hphi]; exact (hm P).2⟩
  refine ⟨{ toFun := fun P => secF ω τ fr (cLoc l τ) Ψ P
            map_add' := fun P Q => by
              funext g
              simp only [secF, hadd, map_add (f := _), Submodule.coe_add, Pi.add_apply]
            map_smul' := fun a P => by
              funext g
              simp only [secF, hsmul, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] },
          { toFun := fun P => thF ω ν τ fr (cLoc l τ) Ψ P
            map_add' := fun P Q => by
              funext g
              simp only [thF, Pi.add_apply]
              rw [hadd]
              exact hTL D n V ψ χ θ μ ω H l s ν _ _ (hstd P) (hstd Q) c.hr g
            map_smul' := fun a P => by
              funext g
              simp only [thF, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
              rw [hsmul]
              exact thetaInt_smul ω ν _ a g }, fun P => rfl, fun P => rfl⟩

end PositivityTheory.Rg.Sw.Glob
end
end

section

namespace PositivityTheory.Rg.Sw.Glob

theorem locOpEx_of_locFact (hF : LocFact) : LocOpEx := locOpEx_of_fact hF awayIn schFP lNe

end PositivityTheory.Rg.Sw.Glob
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace PositivityTheory.Rg.Sw.Glob.AW

variable {D : D7} {n : ℕ}

def AG (θ : InfFam D) (τ : D.what₂.Tau) (x : G D n) : Prop :=
  IsTrivAt θ τ x ∧ ((∃ b, mat x = blk4 1 b 0 1) ∨ (∃ a d, mat x = blk4 a 0 0 d) ∨ (∃ c, mat x = blk4 1 0 c 1))

def AgreeAway {m k : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (x x' : Mx D m k) : Prop :=
  (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') ∧ x.map (finPart D) = x'.map (finPart D)

theorem mem_closure_AG (hG : GenA) (hDA : DecompAway) {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n}
    (hθ : IsInfFam θ) (hι : IsPlaceEmb θ τ ι) (x : G D n) (hx : IsTrivAt θ τ x) :
    x ∈ Submonoid.closure {x : G D n | AG θ τ x} :=
  closure_triv hG hDA hθ hι x hx

theorem exists_w (D : D7) (n : ℕ) : ∃ w : G D n, mat w = blk4 0 1 (-1) 0 := by
  obtain ⟨g, hg⟩ := GlobalTheory.SiegelCells.exists_wPart (D := D) (n := n) n
  refine ⟨g, hg.trans ?_⟩
  have hL : GlobalTheory.SiegelCells.lastDiag (AE D) n n = 1 := by
    unfold GlobalTheory.SiegelCells.lastDiag
    rw [← Matrix.diagonal_one]
    congr 1; funext i; simp
  rw [GlobalTheory.SiegelCells.wMat, hL, sub_self]

theorem compAt_b_zero {θ : InfFam D} {τ : D.what₂.Tau} {x : G D n} {b : Mx D n n} (hx : IsTrivAt θ τ x)
    (h : mat x = blk4 1 b 0 1) : compAt θ τ b = 0 := by
  have h1 : compAt θ τ (mat x) = blk4 1 (compAt θ τ b) 0 1 := by rw [h, component_block_matrix, compAt_one', compAt_zero']
  have h2 : (blk4 1 0 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) = blk4 1 (compAt θ τ b) 0 1 := by
    rw [GlobalTheory.StdUnn.Model.block_matrix_one, ← h1]; exact hx.symm
  exact (GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h2).2.1.symm

theorem compAt_a_one {θ : InfFam D} {τ : D.what₂.Tau} {x : G D n} {a d : Mx D n n} (hx : IsTrivAt θ τ x)
    (h : mat x = blk4 a 0 0 d) : compAt θ τ a = 1 := by
  have h1 : compAt θ τ (mat x) = blk4 (compAt θ τ a) 0 0 (compAt θ τ d) := by rw [h, component_block_matrix, compAt_zero']
  have h2 : (blk4 1 0 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) = blk4 (compAt θ τ a) 0 0 (compAt θ τ d) := by
    rw [GlobalTheory.StdUnn.Model.block_matrix_one, ← h1]; exact hx.symm
  exact (GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h2).1.symm

theorem compAt_mul_of_one {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} (x : Mx D m k) (a : Mx D k k)
    (ha : compAt θ τ a = 1) : compAt θ τ (x ⬝ a : Mx D m k) = compAt θ τ x := by
  rw [compAt_mul', ha, Matrix.mul_one]

theorem agree_mul_right {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} {x x' : Mx D m k} (a : Mx D k k)
    (h : AgreeAway θ τ x x') : AgreeAway θ τ (x ⬝ a : Mx D m k) (x' ⬝ a : Mx D m k) := by
  refine ⟨fun τ' hτ' => ?_, ?_⟩
  · rw [compAt_mul', compAt_mul', h.1 τ' hτ']
  · rw [Matrix.map_mul, Matrix.map_mul, h.2]

theorem unipArg_away {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) (V : HSp D) {b : Mx D n n}
    (hb : compAt θ τ b = 0) {x x' : Mx D V.rank n} (h : AgreeAway θ τ x x') :
    halfTr (Matrix.trace (b ⬝ inner V x x : Mx D n n)) = halfTr (Matrix.trace (b ⬝ inner V x' x' : Mx D n n)) := by
  have htr : ∀ (R : Type) [CommRing R] (f : AE D →+* R) (M : Mx D n n), f (Matrix.trace M) = Matrix.trace (M.map f) := by
    intro R _ f M
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]
    exact map_sum f _ _
  have hinner : ∀ τ'', τ'' ≠ τ → compAt θ τ'' (inner V x x) = compAt θ τ'' (inner V x' x') := by
    intro τ'' hτ''
    have hx := h.1 τ'' hτ''
    have hadj : compAt θ τ'' (adj x) = compAt θ τ'' (adj x') := by
      ext i j
      have := congrFun (congrFun hx j) i
      simp only [compAt_eq, Matrix.map_apply] at this ⊢
      simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
      rw [cθ_cA hθ, cθ_cA hθ, this]
    simp only [GlobalTheory.StdUnn.inner]
    rw [compAt_mul', compAt_mul', compAt_mul', compAt_mul', hadj, hx]
  have hfin : (inner V x x).map (finPart D) = (inner V x' x').map (finPart D) := by
    have hadj : (adj x).map (finPart D) = (adj x').map (finPart D) := by
      ext i j
      have := congrFun (congrFun h.2 j) i
      simp only [Matrix.map_apply] at this ⊢
      simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
      rw [finPart_cA, finPart_cA, this]
    simp only [GlobalTheory.StdUnn.inner]
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hadj, h.2]
  congr 1
  apply ae_ext hθ
  · intro τ''
    rw [htr, htr, ← compAt_eq, ← compAt_eq, compAt_mul', compAt_mul']
    by_cases hτ : τ'' = τ
    · subst hτ; rw [hb, Matrix.zero_mul, Matrix.zero_mul]
    · rw [hinner τ'' hτ]
  · rw [htr, htr, Matrix.map_mul, Matrix.map_mul, hfin]

theorem exists_change_tau {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) {m k : ℕ} (xs x0 : Mx D m k) :
    ∃ x1 : Mx D m k, compAt θ τ x1 = compAt θ τ x0 ∧ AgreeAway θ τ x1 xs := by
  obtain ⟨-, hfin, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt (D := D) hθ τ (compAt θ τ x0 - compAt θ τ xs)
  refine ⟨xs + lineAt θ τ (compAt θ τ x0 - compAt θ τ xs) 1, ?_, fun τ' hτ' => ?_, ?_⟩
  · rw [compAt_add', hcomp 1 τ, if_pos rfl]; simp
  · rw [compAt_add', hcomp 1 τ', if_neg hτ', add_zero]
  · rw [Matrix.map_add _ (map_add (finPart D)), hfin 1, add_zero]

theorem levi_blocks (g : G D n) {a d : Mx D n n} (h : mat g = blk4 a 0 0 d) :
    ∃ a' : GL (Fin n) (AE D), a'.1 = a ∧ d = adj (a'⁻¹).1 := by
  obtain ⟨-, h2, -, -⟩ := GlobalTheory.CompanionTheory.SwUnf.SmallCell.unitary_rel g h
  simp only [adj_zero, Matrix.zero_mul, neg_zero, zero_add] at h2
  have h3 : adj d * a = 1 := by
    have := congrArg adj h2
    rwa [adj_mul, adj_adj, adj_one] at this
  have h4 : a * adj d = 1 := mul_eq_one_comm.mp h3
  refine ⟨⟨a, adj d, h4, h3⟩, rfl, ?_⟩
  show d = adj (adj d)
  rw [adj_adj]

theorem mat_w_conj {w x : G D n} (hw : mat w = blk4 0 1 (-1) 0) {c : Mx D n n} (hx : mat x = blk4 1 0 c 1) :
    mat (w⁻¹ * x * w) = blk4 1 (-c) 0 1 := by
  rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv w hw, hx, hw]
  simp [adj_zero, adj_one, adj_neg, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]

theorem trivAt_conj {θ : InfFam D} {τ : D.what₂.Tau} {x : G D n} (w : G D n) (hx : IsTrivAt θ τ x) :
    IsTrivAt θ τ (w⁻¹ * x * w) := by
  unfold IsTrivAt at *
  have hw : compAt θ τ (mat w⁻¹) * compAt θ τ (mat w) = 1 := by
    rw [← compAt_mul', ← GlobalTheory.StdUnn.LeftInvSect.mat_mul, inv_mul_cancel, GlobalTheory.StdUnn.LeftInvSect.mat_one, compAt_one']
  rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_mul, compAt_mul', compAt_mul', hx, Matrix.mul_one, hw]

theorem exists_compAt {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℂ) :
    ∃ x : Mx D m k, compAt θ τ x = M := by
  obtain ⟨-, -, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt (D := D) hθ τ M
  exact ⟨lineAt θ τ M 1, by rw [hcomp 1 τ, if_pos rfl]; simp⟩

theorem exists_sch_ne {m k : ℕ} (u0 : Fin m → Fin k → ℂ) : ∃ f : (Fin m → Fin k → ℂ) → ℂ, IsSch f ∧ f u0 ≠ 0 := by
  let b : ContDiffBump u0 := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun u => ((b u : ℝ) : ℂ), ?_, ?_⟩
  · have hc : HasCompactSupport (fun u => ((b u : ℝ) : ℂ)) := b.hasCompactSupport.comp_left Complex.ofReal_zero
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun u => ((b u : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
    exact ⟨hc.toSchwartzMap hs, rfl⟩
  · have : b u0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    simp [this]

end PositivityTheory.Rg.Sw.Glob.AW
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem awayNZ : AwayNZ := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  classical
  have hl : ∀ τ', l τ' ≠ 0 := fun τ' => lNe D ψ θ l hC.hψ hC.hθ hC.hl τ'
  let W : AddSubgroup (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | ∀ i j, a i j ∈ intAE D}
      add_mem' := fun ha hb i j => (intAE D).add_mem (ha i j) (hb i j)
      zero_mem' := fun _ _ => (intAE D).zero_mem
      neg_mem' := fun ha i j => (intAE D).neg_mem (ha i j) }
  have hWe : (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  let g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
    if (QuotientAddGroup.mk (show Matrix (Fin V.rank) (Fin n) _ from a) : _ ⧸ W) = 0 then (1 : ℂ) else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  let Ψ : Mx D V.rank n → ℂ := fun x =>
    evalPoly (1 : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) (fun τ => compAt θ τ x) *
      gAway V l s τ (fun τ => compAt θ τ x) * g (fun i j => finPart D (x i j))
  have hΨ : Ψ ∈ awayA θ V n l s τ := Submodule.subset_span ⟨1, g, hg, by simp, rfl⟩
  refine ⟨Ψ, 0, awayIn D n V θ l s τ ε fr hC.hθ hC.hs hC.hfr hl Ψ hΨ, ?_⟩
  have h0 : ∀ τ', compAt θ τ' (0 : Mx D V.rank n) = 0 := fun τ' => by
    ext i j
    simp [compAt]
  have hg0 : g (fun i j => finPart D ((0 : Mx D V.rank n) i j)) = 1 := by
    simp only [g]
    rw [if_pos]
    simp only [Matrix.zero_apply, map_zero]
    exact (QuotientAddGroup.eq_zero_iff (N := W) (0 : Matrix (Fin V.rank) (Fin n) _)).2 W.zero_mem
  show evalPoly _ _ * gAway V l s τ _ * g _ ≠ 0
  rw [hg0]
  simp only [evalPoly, map_one, one_mul, mul_one, gAway, h0]
  simp

end PositivityTheory.Rg.Sw.Glob
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

namespace PositivityTheory.Rg.Sw.Glob

theorem tensInj_of : AwayIn → TensInj := by
  intro hAI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC f g h
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  have hΨ := LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ
  have hcls := hAI D n V θ l s τ ε fr hC.hθ hC.hs hC.hfr (LocLawH.cx_lne hC) _ hΨ
  exact LocLawH.tens_cancel hσ V l s τ hC.hfr.1 (h _ hcls)

theorem lawN_of : UnipTau → TensInj → LawN := by
  intro hU hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL y b hb hy f hf
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC _ _ fun Ψ hΨ => ?_
  rw [← hL.2 y Ψ hΨ f hf]
  funext x
  rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y b hb hy]
  simp only [tens, chN]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end
