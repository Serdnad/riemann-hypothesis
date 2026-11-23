module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle292
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem cont_of_val {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k]
    [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (h : Continuous fun g => (r g : Matrix (Fin n) (Fin n) k)) : Continuous r := by
  rw [Units.continuous_iff]
  refine ⟨h, ?_⟩
  have e : (fun g => (((r g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
      (fun g => (r g : Matrix (Fin n) (Fin n) k)) ∘ fun g => g⁻¹ := by
    funext g
    simp [map_inv]
  rw [e]
  exact h.comp continuous_inv

private theorem val_cont {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} :
    Continuous fun x : GL (Fin n) k => (x : Matrix (Fin n) (Fin n) k) := Units.continuous_val

private theorem sumRep_entry {Γ k : Type} [Group Γ] [Field k] {a b : ℕ} (r : Γ →* GL (Fin a) k)
    (s : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin a) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) =
      (r g : Matrix (Fin a) (Fin a) k) i j := by
  have hi : finSumFinEquiv.symm (Fin.castAdd b i) = Sum.inl i := finSumFinEquiv_symm_apply_castAdd i
  have hj : finSumFinEquiv.symm (Fin.castAdd b j) = Sum.inl j := finSumFinEquiv_symm_apply_castAdd j
  simp [sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom, Matrix.reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj]
  rfl

theorem UpperTheory.Gal.TP.Sub.contLeft_holds :
    ContLeft := by
  intro Γ k _ _ _ _ _ _ a b
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s hc
    apply cont_of_val r
    have hm : Continuous fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) := val_cont.comp hc
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have he : Continuous fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) :=
      (continuous_apply _).comp ((continuous_apply _).comp hm)
    refine he.congr fun g => ?_
    exact sumRep_entry r s g i j
  · rintro r r' ⟨u, hu⟩ hr
    have hf : (⇑r') = fun x => u * r x * u⁻¹ := funext hu
    rw [hf]
    exact (continuous_const.mul hr).mul continuous_const
  · intro r c hr hc
    apply cont_of_val
    have hv : (fun g => ((tw r c g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)) = fun g => ((c g : kˣ) : k) • (r g : Matrix (Fin a) (Fin a) k) := by
      funext g
      exact UpperTheory.V.Af.tw_val r c g
    rw [hv]
    exact (Units.continuous_val.comp hc).smul (val_cont.comp hr)
  · intro c hc
    apply cont_of_val
    have hv : (fun g => ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) = fun g => Matrix.diagonal fun _ => ((c g : kˣ) : k) := by
      funext g
      simp [rk1, Matrix.scalar_apply]
    rw [hv]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val.comp hc)
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open Formalism.MainNotions.SumRepresentations.At (sumRep)

namespace UpperTheory.Gal.TP.Sub

theorem denseId_holds : CpFacts → DgFacts → DenseId := by
  intro _ _ Γ _ _ l _ m m' t t' r r' a a' hr hr' ha ha' D hD hEq g
  apply Polynomial.funext
  intro x
  have key : ∀ {n : ℕ} (s : Γ →* GL (Fin n) (Qbar l)), Continuous s →
      Continuous fun g => (cp s g).eval x := by
    intro n s hs
    simp only [cp, Matrix.eval_charpoly]
    exact (continuous_const.sub (Units.continuous_val.comp hs)).matrix_det
  have keyl : ∀ {n : ℕ} (b : Fin n → Γ →* (Qbar l)ˣ), (∀ i, Continuous (b i)) →
      Continuous fun g => (lin b g).eval x := by
    intro n b hb
    simp only [lin, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    exact continuous_finsetProd _ fun i _ =>
      continuous_const.sub (Units.continuous_val.comp (hb i))
  have h := Continuous.ext_on hD ((key r hr).mul (keyl a' ha')) ((key r' hr').mul (keyl a ha))
    (fun g hg => by
      simp only [Pi.mul_apply]
      rw [← Polynomial.eval_mul, ← Polynomial.eval_mul, hEq g hg])
  have hg := congrFun h g
  simp only [Pi.mul_apply] at hg
  rw [Polynomial.eval_mul, Polynomial.eval_mul]
  exact hg

end UpperTheory.Gal.TP.Sub

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem satPol_val (q a : ℕ) (b : ℂˣ) (m : ℤ) :
    ((((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) * (b : ℂ)) ^ (-m) =
      ((q : ℂ) ^ ((((1 : ℝ) - a) / 2 : ℝ) : ℂ)) ^ m * ((b : ℂ)⁻¹) ^ m := by
  have hx : ((((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ))⁻¹ = (q : ℂ) ^ ((((1 : ℝ) - a) / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q), Complex.ofReal_natCast, ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  rw [zpow_neg, ← inv_zpow, mul_inv, ← hx, mul_zpow]

theorem UpperTheory.Gal.TP.Sub.satPol_holds :
    SatPol := by
  intro E Ω _ _ _ _ _ A w h a B g
  rw [GlobalTheory.SatChar.charPol_satWD]
  unfold unrPol algSat
  simp only [bind, pure, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]
  congr 1
  refine Multiset.map_congr rfl fun b _ => ?_
  rw [satPol_val]
end
