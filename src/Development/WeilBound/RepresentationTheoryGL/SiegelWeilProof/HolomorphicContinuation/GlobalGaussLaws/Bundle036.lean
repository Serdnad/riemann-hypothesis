module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlaceFacts
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PsiInnerSIns
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle214
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC mat_ext psiT_sigR finPart_sigR)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}


theorem compAt_sub_sIns {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    (hdet : IsUnit fr.det) (y : Mx D m n) :
    (y - sIns τ fr (piF θ τ fr y)).map (psiT D τ) = 0 := by
  have hp : Matrix.of (piF θ τ fr y) = fr⁻¹ * compAt θ τ y := rfl
  rw [Matrix.map_sub (psiT D τ) (fun a b => map_sub (psiT D τ) a b), ← PlaceFactsH.compAt_eq_psiT hθ,
    ← PlaceFactsH.compAt_eq_psiT hθ, show sIns (D := D) τ fr (piF θ τ fr y) = insT τ (fr * Matrix.of (piF θ τ fr y)) from rfl,
    compAt_insT hθ, if_pos rfl, hp, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul, sub_self]



theorem inner_away {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} (x x' z : Mx D V.rank n)
    (hx : ∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') (hf : x.map (finPart D) = x'.map (finPart D))
    (hz : z.map (psiT D τ) = 0) : inner V x z = inner V x' z := by
  apply mat_ext D
  · intro τ''
    rw [map_inner, map_inner]
    by_cases h : τ'' = τ
    · subst h; rw [hz, Matrix.mul_zero, Matrix.mul_zero, Matrix.mul_zero]
    · have := hx τ'' h
      rw [eq_thetaC D hθ] at this
      change x.map (psiT D τ'') = x'.map (psiT D τ'') at this
      rw [this]
  · have ha : (adj x).map (finPart D) = (adj x').map (finPart D) := by
      ext i j
      simp only [adj, Matrix.map_apply, Matrix.transpose_apply, cA]
      rw [finPart_sigR, finPart_sigR]
      congr 1
      exact congrFun (congrFun hf j) i
    show (adj x * (gA V * z)).map (finPart D) = (adj x' * (gA V * z)).map (finPart D)
    rw [Matrix.map_mul, ha, ← Matrix.map_mul]

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

section

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace PositivityTheory.Rg.Sw.Glob.GenUnitH

variable {D : D7}

theorem compAt_eq (v : GlobalTheory.FinPl.Pl D) (z : AE D) :
    GlobalTheory.FinPl.compAt D v z = GlobalTheory.AdelicU.compFin D.host.F D.host.E v z :=
  GlobalTheory.EmbChart.map_evalV_map_sndA v z

theorem compFin_tensAt_ne {v w : GlobalTheory.FinPl.Pl D} (h : w ≠ v) (y : Ev D v) :
    GlobalTheory.AdelicU.compFin D.host.F D.host.E w (GlobalTheory.EmbChart.tensAt D.host.E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  | tmul a x =>
    show GlobalTheory.AdelicU.evFin D.host.F w (GlobalTheory.EmbChart.atPlace v a) ⊗ₜ[D.host.F] x = 0
    rw [show GlobalTheory.AdelicU.evFin D.host.F w (GlobalTheory.EmbChart.atPlace v a) = 0 from GlobalTheory.AdelicU.evalV_singleFin_ne h a,
      TensorProduct.zero_tmul]

theorem infPart_tensAt (v : GlobalTheory.FinPl.Pl D) (y : Ev D v) : infPart D (GlobalTheory.EmbChart.tensAt D.host.E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  | tmul a x =>
    show fstA D.host.F (GlobalTheory.EmbChart.atPlace v a) ⊗ₜ[D.host.F] x = 0
    rw [show fstA D.host.F (GlobalTheory.EmbChart.atPlace v a) = 0 from rfl, TensorProduct.zero_tmul]

theorem tensAt_mem_idAt (v : GlobalTheory.FinPl.Pl D) (y : Ev D v) :
    GlobalTheory.EmbChart.tensAt D.host.E v y ∈ GlobalTheory.FinPl.idAt D (· = v) := by
  unfold GlobalTheory.FinPl.idAt
  refine Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (infPart_tensAt v y), ?_⟩
  refine (Submodule.mem_iInf _).2 fun w => RingHom.mem_ker.2 ?_
  rw [compAt_eq]
  exact compFin_tensAt_ne w.2 y

theorem tensAt_mem_intAt (v : GlobalTheory.FinPl.Pl D) (y : Ev D v) (hy : y ∈ intLoc D.host.F D.host.E v) :
    GlobalTheory.EmbChart.tensAt D.host.E v y ∈ GlobalTheory.FinPl.intAt D (· = v) :=
  ⟨tensAt_mem_idAt v y, (GlobalTheory.EmbChart.finPart_tensAt_mem_iff y).2 hy⟩

theorem glueEntry (z : ∀ v : GlobalTheory.FinPl.Pl D, Ev D v) (hz : ∀ v, z v ∈ intLoc D.host.F D.host.E v) :
    ∃ s : AE D, infPart D s = 0 ∧ ∀ v, GlobalTheory.FinPl.compAt D v s = z v := by
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.FinPlLoc.glue D (fun v => GlobalTheory.EmbChart.tensAt D.host.E v (z v))
    (fun v => tensAt_mem_idAt v (z v)) ⟨∅, fun v _ => tensAt_mem_intAt v (z v) (hz v)⟩
  refine ⟨s, hs0, fun v => ?_⟩
  have h := hs v
  unfold GlobalTheory.FinPl.idOff at h
  have h2 : GlobalTheory.FinPl.compAt D v (s - GlobalTheory.EmbChart.tensAt D.host.E v (z v)) = 0 :=
    RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 h ⟨v, rfl⟩)
  rw [map_sub, sub_eq_zero, compAt_eq v (GlobalTheory.EmbChart.tensAt _ v _), GlobalTheory.EmbChart.compFin_tensAt] at h2
  exact h2

theorem finExt {x y : Af D.host.F ⊗[D.host.F] D.host.E}
    (h : ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v x = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v y) : x = y := by
  have key : ∀ (x : Af D.host.F ⊗[D.host.F] D.host.E) (v : GlobalTheory.FinPl.Pl D) (k : Fin 2),
      (Algebra.TensorProduct.basis (Fv D.host.F v) (Formalism.IndefR.Eqv.basE D)).repr (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v x) k =
        evalV D.host.F v ((Formalism.IndefR.Eqv.basAf D).repr x k) := by
    intro x v k
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), Finsupp.add_apply, ha, hb]
    | tmul a e =>
      show (Algebra.TensorProduct.basis (Fv D.host.F v) (Formalism.IndefR.Eqv.basE D)).repr
        (evalV D.host.F v a ⊗ₜ[D.host.F] e) k = _
      rw [Formalism.IndefR.Eqv.basAf, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
      simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  apply (Formalism.IndefR.Eqv.basAf D).ext_elem
  intro k
  apply GlobalTheory.AdelicU.af_ext
  intro u
  rw [← key, ← key, h]

end PositivityTheory.Rg.Sw.Glob.GenUnitH

namespace PositivityTheory.Rg.Sw.Glob

theorem unitAE : UnitAE := by
  intro D d hτ hv
  choose z' hz'mem hz'inv using fun v => (hv v).2
  obtain ⟨s, -, hs⟩ := GenUnitH.glueEntry z' hz'mem
  let x := Formalism.IndefR.Eqv.glueA D (Formalism.IndefR.Eqv.splitInv D fun τ => (Formalism.IndefR.Eqv.psiT D τ d)⁻¹) (finPart D s)
  have hx : ∀ v, GlobalTheory.FinPl.compAt D v x = z' v := fun v => by
    show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (finPart D x) = _
    rw [Formalism.IndefR.Eqv.finPart_glueA]
    exact hs v
  have hdx : d * x = 1 := by
    apply Formalism.IndefR.Eqv.ae_ext' D
    · intro τ
      rw [map_mul, Formalism.IndefR.Eqv.psiT_glueA, mul_inv_cancel₀ (hτ τ), map_one]
    · apply GenUnitH.finExt
      intro v
      show GlobalTheory.FinPl.compAt D v (d * x) = GlobalTheory.FinPl.compAt D v 1
      rw [map_mul, map_one, hx v, hz'inv v]
  exact ⟨⟨d, x, hdx, by rw [mul_comm]; exact hdx⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob
end
end
