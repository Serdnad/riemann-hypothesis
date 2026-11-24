module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperLeftBlockEqOneIffOfMemBlockTri

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult



namespace GlobalTheory.SeriesTie.LevKProof

variable {D : D7}

theorem blkOf_zero_of_le {n r t : ℕ} (h : n ≤ r) : (blkOf r t : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blkOf]
  rw [if_pos (by omega)]

theorem secondBlockIndex_eq_zero_of_dim_le {n r : ℕ} (h : n ≤ r) : (blk2 r : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blk2]
  rw [if_pos (by omega)]

theorem mem_blockTriangular_singleBlock_of_le {n r : ℕ} {κ : Type} [CommRing κ] (h : n ≤ r) (g : GL (Fin n) κ) :
    g ∈ blockTri (blk2 r) := by
  intro i k hik
  rw [secondBlockIndex_eq_zero_of_dim_le h] at hik
  exact absurd hik (lt_irrefl _)

end GlobalTheory.SeriesTie.LevKProof

namespace GlobalTheory.SeriesTie


open LevKProof in
theorem levK_eq_levG_triv : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw}, RealPin Rl cG ρ → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ρ.levK i j b = levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) := by
  apply _root_.GlobalTheory.PrincipalLevel.levK_eq_levG <;> assumption

end GlobalTheory.SeriesTie
