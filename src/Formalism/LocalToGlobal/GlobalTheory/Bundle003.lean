module

public import Formalism.LocalToGlobal.GlobalTheory.Bundle001
public import Formalism.LocalToGlobal.GlobalTheory.DivPassageP
public import Formalism.LocalToGlobal.GlobalTheory.FamCol
public import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount
public import Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.SizeWindowBrackets.FirstPrimeNeSecondPrime
import Formalism.SizeWindowBrackets.Bundle002
import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
import Formalism.SizeWindowBrackets.SChain

@[expose] public section

section

set_option linter.style.haveILetI false

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.DivPassage2

open Formalism.L2.Indef Formalism.L2.GlobalTheoryTheory.DivPassage

section Chars

variable {K : Type} [Field K] {Γ : Type} [Group Γ] [Finite Γ]

end Chars

section TP

variable {K : Type} [Field K] {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ}

variable [NumberField K]

end TP

section Norms

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)

end Norms

section Adj

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ}
  (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)

end Adj

section Lat

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {D0 D1 : ℕ} (A : LevelAmb K D0 D1)

end Lat

section Gen

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {D0 D1 : ℕ} (A : LevelAmb K D0 D1)

theorem rows_gen (hL : A.LatG) {D : ℕ} (ι : Matrix (Fin A.Dg) (Fin D) K) (P : Matrix (Fin A.Dg) (Fin A.Dg) K)
    (hD : 0 < D) (hinj : Function.Injective ι.mulVec) (hr : LinearMap.range ι.mulVecLin = LinearMap.range P.mulVecLin) :
    A.partLat P ≠ ⊥ := by
  intro hb
  have hspan := A.span_partLat hL P
  rw [hb, Submodule.bot_coe, Submodule.span_zero_singleton] at hspan
  obtain ⟨x, hx⟩ : ∃ x : Fin D → K, x ≠ 0 := ⟨fun _ => 1, fun h => one_ne_zero (congrFun h ⟨0, hD⟩)⟩
  have hmem : ι *ᵥ x ∈ LinearMap.range P.mulVecLin := by
    rw [← hr]
    exact ⟨_, rfl⟩
  rw [← hspan, Submodule.mem_bot] at hmem
  exact hx (hinj (by rw [hmem, Matrix.mulVec_zero]))

end Gen

section Triv

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Triv

end Formalism.L2.GlobalTheoryTheory.DivPassage2
end
end

section

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamColC

open Formalism Formalism.HN Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.FamCol

section Obj

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

structure RowTr [Fintype I] (C : ColObj K I) (R : RowArg C) (x ε : ℝ) : Prop where
  X' : ∀ w, IsUnit (R.X' w).det
  Y : ∀ u, IsUnit (R.Y u).det
  Y' : IsUnit R.Y'.det
  cc_fg : R.cc.FG
  cc_span : Submodule.span K (R.cc : Set R.Wd) = ⊤
  into : ∀ u, (C.Npr u).map ((R.B u).restrictScalars (𝓞 K)) ≤ R.cc
  ht : ∀ u, R.B u ≠ 0 → htMap (C.M u).b (C.M u).X R.b' R.X' (R.B u) ≤ R.h u
  block : ∀ u (k : R.κ) (j : (C.M u).ι), R.Ball u (Sum.inl k) j =
    (R.Y'⁻¹ * (LinearMap.toMatrix (C.M u).b R.b' (R.B u)).map R.v.embedding * R.Y u) k j
  γ : ∀ u, 0 < R.γ u
  Ball : ∀ u, R.Ball u = R.Bf u * C.Vr u R.v
  η0_ge : -1 ≤ R.η0
  η0_le : R.η0 ≤ LChain6.E8 x ε
  η1_le : R.η1 ≤ LChain6.E8 x ε
  exponent_bound_ter : 0 ≤ R.e0
  sqrt_error_le_half : Real.sqrt R.e0 ≤ LChain6.E8 x ε
  inputS : MatrixLatticeEstimates.InputSG R.Bf R.γ C.Dstar R.η0 R.η1 R.e0
  irr : (1 - LChain6.E7 x ε) * (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) ≤ (Fintype.card R.κ : ℝ)

end Obj

section Fam7

variable {H : Type} {W : H → Type}

end Fam7

section Collected

open Formalism.L2.Indef Formalism.L2.DIV Formalism.DivisionValues

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}
  {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}

end Collected

section Family

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.LChain6

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end Family

section Core

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.LChain6

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end Core

end Formalism.L2.GlobalTheoryTheory.FamColC

end
end
