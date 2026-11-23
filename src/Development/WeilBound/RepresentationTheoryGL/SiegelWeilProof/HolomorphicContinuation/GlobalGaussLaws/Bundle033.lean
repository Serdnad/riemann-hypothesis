module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle015
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle027
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle019
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle031
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle029
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle016
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle023
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle025

@[expose] public section

section

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

abbrev Ev (D : D7) (v : GlobalTheory.FinPl.Pl D) := Fv D.host.F v ⊗[D.host.F] D.host.E

def IsIntUnit {D : D7} {v : GlobalTheory.FinPl.Pl D} (z : Ev D v) : Prop :=
  z ∈ intLoc D.host.F D.host.E v ∧ ∃ z' ∈ intLoc D.host.F D.host.E v, z * z' = 1

def cTv {D : D7} {v : GlobalTheory.FinPl.Pl D} (a : Matrix (Fin n) (Fin n) (Ev D v)) : Matrix (Fin n) (Fin n) (Ev D v) :=
  (a.map (sigR (Fv D.host.F v) D.sp.cm.sig)).transpose

def LocGood {D : D7} {v : GlobalTheory.FinPl.Pl D} (kv : Matrix (Fin (n + n)) (Fin (n + n)) (Ev D v))
    (a : Matrix (Fin n) (Fin n) (Ev D v)) (I : Finset (Fin n)) : Prop :=
  (∀ i j, a i j ∈ intLoc D.host.F D.host.E v) ∧ IsIntUnit a.det ∧
    IsIntUnit (blkDm (kv * blk4 a 0 0 (cTv a)⁻¹ * wIm I)).det

def LocFin : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, ∀ v : GlobalTheory.FinPl.Pl D,
    ∃ (a : Matrix (Fin n) (Fin n) (Ev D v)) (I : Finset (Fin n)), LocGood ((mat k).map (GlobalTheory.FinPl.compAt D v)) a I

def GlueLevi : Prop :=
  ∀ (D : D7) (n : ℕ) (a : ∀ v : GlobalTheory.FinPl.Pl D, Matrix (Fin n) (Fin n) (Ev D v)),
    (∀ v i j, a v i j ∈ intLoc D.host.F D.host.E v) → (∀ v, IsIntUnit (a v).det) →
    ∃ m : G D n, m ∈ genSet D n ∧ (∀ v, (mat m).map (GlobalTheory.FinPl.compAt D v) = blk4 (a v) 0 0 (cTv (a v))⁻¹) ∧
      ∀ τ, (mat m).map (Formalism.IndefR.Eqv.psiT D τ) = 1

def GlueW : Prop :=
  ∀ (D : D7) (n : ℕ) (I : GlobalTheory.FinPl.Pl D → Finset (Fin n)),
    ∃ w ∈ Subgroup.closure (genSet D n), (∀ v, (mat w).map (GlobalTheory.FinPl.compAt D v) = wIm (I v)) ∧
      ∀ τ, (mat w).map (Formalism.IndefR.Eqv.psiT D τ) = 1

def UnitAE : Prop :=
  ∀ (D : D7) (d : AE D), (∀ τ, Formalism.IndefR.Eqv.psiT D τ d ≠ 0) → (∀ v, IsIntUnit (GlobalTheory.FinPl.compAt D v d)) → IsUnit d

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

namespace PositivityTheory.Rg.Sw.Glob.VacJ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC
  PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacE PositivityTheory.Rg.Sw.Glob.VacF PositivityTheory.Rg.Sw.Glob.VacG PositivityTheory.Rg.Sw.Glob.VacH
  PositivityTheory.Rg.Sw.Glob.VacI

variable {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
  {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
  {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}

theorem rhoT_sq {m : ℕ} (t : ℝ) (ε : Fin m → Bool) (a : Fin m) : (rhoT t ε a) ^ 2 = 1 := by
  unfold rhoT; split_ifs <;> norm_num

theorem rot_gen (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (hl0 : l τ ≠ 0) (hN : LawN) (hNb : LawNbar) (hLM : LocMul)
    (hGZ : GZSch) (L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ))
    (hL : IsLocFact ω τ fr ι L) (e : ℤ)
    (hlev : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f)
    (φ : Fin n → ℝ) (hφ : ∀ j, -(Real.pi / 2) < φ j ∧ φ j ≤ Real.pi / 2) (K : ℂ) :
    L (mkG (kth φ) (inK_kth φ).1) (DG K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (K * ∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ)))
        (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
  have hc : ∀ j, 0 < Real.cos (φ j / 2) := fun j =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [(hφ j).1, Real.pi_pos], by linarith [(hφ j).2, Real.pi_pos]⟩
  have hk : mkG (kth φ) (inK_kth φ).1 = mkG (kth fun j => φ j / 2) (inK_kth _).1 * mkG (kth fun j => φ j / 2) (inK_kth _).1 := by
    apply Subtype.ext; apply Units.ext; exact kth_half φ
  have hf0 : IsSch (DG (n := n) K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) :=
    isSch_DG hGZ ε (tLoc l τ) (cLoc l τ) (cpos hl0) tabs K
  rw [hk, hLM D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL _ _ _ hf0,
    rot_DG hC hl0 hN hNb hLM hGZ L hL e hlev _ hc K, rot_DG hC hl0 hN hNb hLM hGZ L hL e hlev _ hc _]
  congr 1
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact dbl_angle _ _ (rhoT_sq _ _ a)

end PositivityTheory.Rg.Sw.Glob.VacJ
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

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

theorem mat_mOf {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {τ : D.what₂.Tau}
    {ι : PositivityTheory.Rg.Sw.GR n →* G D n} (hι : IsPlaceEmb θ τ ι) (A : GL (Fin n) ℂ) :
    mat (ι (mOf A)) = blk4 (unitAt hσ τ A).1 0 0 (adj ((unitAt hσ τ A)⁻¹).1) := by
  have hU : ((unitAt hσ τ A).1).map (finPart D) = 1 := by
    rw [unitAt_val]
    exact finite_part_adelic_point_matrix hσ τ A.1
  have hUi : (((unitAt hσ τ A)⁻¹).1).map (finPart D) = 1 := finite_part_adelic_point_matrix hσ τ (A⁻¹).1
  refine ext_mx hσ ?_ ?_
  · rw [(hι.2 (mOf A)).2.2, finite_part_block_matrix_map, hU, finPart_adj _ hUi, Matrix.map_zero _ (map_zero _), block_matrix_diagonal_one_eq_one]
  · intro τ'
    by_cases e : τ' = τ
    · rw [e, (hι.2 (mOf A)).1, mR_mOf, component_block_matrix (R := ℂ), compAt_adj hσ.inf, unitAt_val, component_adelic_point_matrix hσ,
        compAt_zero]
      have hUc : compAt θ τ ((unitAt hσ τ A)⁻¹).1 = (A⁻¹).1 := component_adelic_point_matrix hσ τ (A⁻¹).1
      rw [hUc]
      rfl
    · rw [(hι.2 (mOf A)).2.1 τ' e, component_block_matrix (R := ℂ), compAt_adj hσ.inf, unitAt_val, component_adelic_point_ne hσ e,
        compAt_zero]
      have hUc : compAt θ τ' ((unitAt hσ τ A)⁻¹).1 = 1 := component_adelic_point_ne hσ e (A⁻¹).1
      rw [hUc, Matrix.conjTranspose_one, block_matrix_diagonal_one_eq_one]

theorem mat_nOf {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {τ : D.what₂.Tau}
    {ι : PositivityTheory.Rg.Sw.GR n →* G D n} (hι : IsPlaceEmb θ τ ι) (y : PositivityTheory.Rg.Sw.GR n) (b : Matrix (Fin n) (Fin n) ℂ)
    (hy : mR y = Matrix.fromBlocks 1 b 0 1) : mat (ι y) = blk4 1 (atT σ τ b) 0 1 := by
  refine ext_mx hσ ?_ ?_
  · rw [(hι.2 y).2.2, finite_part_block_matrix_map, finPart_atT_map hσ τ b, Matrix.map_zero _ (map_zero _),
      Matrix.map_one _ (map_zero _) (map_one _), block_matrix_diagonal_one_eq_one]
  · intro τ'
    by_cases e : τ' = τ
    · rw [e, (hι.2 y).1, hy, component_block_matrix (R := ℂ), compAt_one, compAt_atT hσ, compAt_zero]
      rfl
    · rw [(hι.2 y).2.1 τ' e, component_block_matrix (R := ℂ), compAt_one, compAt_atT_ne hσ e, compAt_zero, block_matrix_diagonal_one_eq_one]

end PositivityTheory.Rg.Sw.Glob.LocLawH
end
end
