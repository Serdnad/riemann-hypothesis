module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.ConvEqOfIsROp
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OrthogonalKeepingHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ConvTest
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle003
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle002
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

private theorem position_in {Z T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} {e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))} {w : Pl E} (h : w ∈ Z) :
    intersection_update_fsHerm_neg_one Z T φ e w = φ w := by simp [intersection_update_fsHerm_neg_one, h]

private theorem slot_eq_fn2_of_not_mem_of_mem {Z T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} {e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))} {w : Pl E} (h : w ∉ Z) (h' : w ∈ T) :
    intersection_update_fsHerm_neg_one Z T φ e w = fn2 a b w (e w) := by simp [intersection_update_fsHerm_neg_one, h, h']

private theorem position_out {Z T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} {e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))} {w : Pl E} (h : w ∉ Z) (h' : w ∉ T) :
    intersection_update_fsHerm_neg_one Z T φ e w = (K2 a b w : Set _).indicator 1 := by simp [intersection_update_fsHerm_neg_one, h, h']

private theorem heckeFunction_mul (w : Pl E) (x y : Ex (Fin (a + 1) × Fin (b + 1))) :
    fn2 a b w (x.mul y) = PositivityTheory.Rg.BcN.F2.mconv (fn2 a b w x) (fn2 a b w y) := by
  funext m
  simp only [fn2, Ex.fn, PositivityTheory.Rg.BcN.F2.mconv]

private theorem heckeFunction_one (w : Pl E) : fn2 a b w (.one : Ex (Fin (a + 1) × Fin (b + 1))) = (K2 a b w : Set _).indicator 1 := rfl

private theorem heckeFunction_isHecke (w : Pl E) (e : Ex (Fin (a + 1) × Fin (b + 1))) : IsHecke (K2 a b w) (fn2 a b w e) :=
  Asm.exHecke2 E a b w e

private theorem ind_hecke (w : Pl E) : IsHecke (K2 a b w) ((K2 a b w : Set _).indicator 1) := heckeFunction_isHecke w .one

private theorem ind_ind (w : Pl E) : PositivityTheory.Rg.BcN.F2.mconv ((K2 a b w : Set _).indicator 1) ((K2 a b w : Set _).indicator 1) =
    ((K2 a b w : Set _).indicator 1 : GLw a w × GLw b w → ℂ) :=
  ((locAlg E a b ∅ ⟨fun w => KGL w (n := a), fun w => KGL w (n := b), fun w => (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1,
    fun w => (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1, fun _ => le_rfl, fun _ => le_rfl, fun _ _ => ⟨rfl, rfl⟩⟩ w).2.2.2.2 _ (ind_hecke w)).1

variable {Z : Finset (Pl E)} (L : Lv a b Z)

private theorem position_hecke {T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} (hφ : L.Fix φ)
    (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    IsHecke ((L.L₁ w).prod (L.L₂ w)) (intersection_update_fsHerm_neg_one Z T φ e w) := by
  by_cases hZ : w ∈ Z
  · rw [position_in hZ]; exact hφ w hZ
  · obtain ⟨h₁, h₂⟩ := L.off w hZ
    rw [h₁, h₂]
    by_cases hT : w ∈ T
    · rw [slot_eq_fn2_of_not_mem_of_mem hZ hT]; exact heckeFunction_isHecke w _
    · rw [position_out hZ hT]; exact ind_hecke w

private theorem ln_fix : L.Fix L.ln := fun w _ => (locAlg E a b Z L w).1

private theorem position_ln {T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} (hφ : L.Fix φ)
    (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T φ e w) (L.ln w) = intersection_update_fsHerm_neg_one Z T φ e w :=
  ((locAlg E a b Z L w).2.2.2.1 _ (position_hecke L hφ e w)).1

private theorem ln_position {T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} (hφ : L.Fix φ)
    (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (L.ln w) (intersection_update_fsHerm_neg_one Z T φ e w) = intersection_update_fsHerm_neg_one Z T φ e w :=
  ((locAlg E a b Z L w).2.2.2.1 _ (position_hecke L hφ e w)).2

private theorem ln_ln (w : Pl E) : PositivityTheory.Rg.BcN.F2.mconv (L.ln w) (L.ln w) = L.ln w :=
  ((locAlg E a b Z L w).2.2.2.1 _ (locAlg E a b Z L w).1).1

private theorem position_one (T : Finset (Pl E)) : intersection_update_fsHerm_neg_one Z T L.ln (fun _ => .one) = L.ln := by
  funext w
  by_cases hZ : w ∈ Z
  · exact position_in hZ
  · have h := (locAlg E a b Z L w).2.2.1 hZ
    by_cases hT : w ∈ T
    · rw [slot_eq_fn2_of_not_mem_of_mem hZ hT, heckeFunction_one, h]
    · rw [position_out hZ hT, h]

private theorem position_empty (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) : intersection_update_fsHerm_neg_one Z ∅ L.ln e = L.ln := by
  funext w
  by_cases hZ : w ∈ Z
  · exact position_in hZ
  · rw [position_out hZ (Finset.notMem_empty w), (locAlg E a b Z L w).2.2.1 hZ]

private theorem position_mul {T : Finset (Pl E)} {φ : ∀ w : Pl E, LF a b w} (hφ : L.Fix φ)
    (e e' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T φ e w) (intersection_update_fsHerm_neg_one Z T L.ln e' w) = intersection_update_fsHerm_neg_one Z T φ (fun w => (e w).mul (e' w)) w := by
  by_cases hZ : w ∈ Z
  · rw [position_in hZ, position_in hZ, position_in hZ]
    exact ((locAlg E a b Z L w).2.2.2.1 _ (hφ w hZ)).1
  · by_cases hT : w ∈ T
    · rw [slot_eq_fn2_of_not_mem_of_mem hZ hT, slot_eq_fn2_of_not_mem_of_mem hZ hT, slot_eq_fn2_of_not_mem_of_mem hZ hT, heckeFunction_mul]
    · rw [position_out hZ hT, position_out hZ hT, position_out hZ hT, ind_ind]

private theorem position_insert {T : Finset (Pl E)} {w : Pl E} (hw : w ∉ T)
    (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (x : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z {w} L.ln e x) (intersection_update_fsHerm_neg_one Z T L.ln e x) = intersection_update_fsHerm_neg_one Z (insert w T) L.ln e x := by
  by_cases hZ : x ∈ Z
  · rw [position_in hZ, position_in hZ, position_in hZ]
    exact ln_ln L x
  · by_cases hx : x = w
    · subst hx
      rw [slot_eq_fn2_of_not_mem_of_mem hZ (Finset.mem_singleton_self x), position_out hZ hw, slot_eq_fn2_of_not_mem_of_mem hZ (Finset.mem_insert_self x T)]
      exact ((locAlg E a b Z L x).2.2.2.2 _ (heckeFunction_isHecke x _)).1
    · by_cases hT : x ∈ T
      · rw [position_out hZ (by simpa using hx), slot_eq_fn2_of_not_mem_of_mem hZ hT, slot_eq_fn2_of_not_mem_of_mem hZ (Finset.mem_insert_of_mem hT)]
        exact ((locAlg E a b Z L x).2.2.2.2 _ (heckeFunction_isHecke x _)).2.1
      · rw [position_out hZ (by simpa using hx), position_out hZ hT, position_out hZ (by simp [hx, hT]), ind_ind]

end

theorem hkMul : HkMul := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ
  have hF := (ffAlg E a b l₁ l₂ D A S hS).2
  have hT := positionTest E a b S Z L hZ
  have hln : IsTestP L.ln := hT.2.1
  have hfix : L.Fix L.ln := ln_fix L
  have hs : ∀ T φ e, L.Fix φ → IsTestP (intersection_update_fsHerm_neg_one Z T φ e) := fun T φ e h => (hT.2.2 φ h).2 T e
  have hsl : ∀ T e, IsTestP (intersection_update_fsHerm_neg_one Z T L.ln e) := fun T e => hs T L.ln e hfix
  refine ⟨(hF _ _ hln hln).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show mulF A.ν (A.ff S L.ln L.ln) (A.ff S L.ln L.ln) = A.ff S L.ln L.ln
    rw [(hF _ _ hln hln).2.2.2.2 _ _ hln hln]
    exact congrArg₂ (A.ff S) (funext (ln_ln L)) (funext (ln_ln L))
  · show adjF (A.ff S L.ln L.ln) = A.ff S L.ln L.ln
    rw [(hF _ _ hln hln).2.1]
    have h : (fun w => lfStar (L.ln w)) = L.ln := funext fun w => (locAlg E a b Z L w).2.1
    rw [h]
  · intro T
    show A.ff S (intersection_update_fsHerm_neg_one Z T L.ln fun _ => .one) (intersection_update_fsHerm_neg_one Z T L.ln fun _ => .one) = A.ff S L.ln L.ln
    rw [position_one L T]
  · intro e₁ e₂
    show A.ff S (intersection_update_fsHerm_neg_one Z ∅ L.ln e₁) (intersection_update_fsHerm_neg_one Z ∅ L.ln e₂) = A.ff S L.ln L.ln
    rw [position_empty L, position_empty L]
  · intro T φ e₁ e₂ hφ
    have t₁ := hs T φ e₁ hφ
    have t₂ := hsl T e₂
    refine ⟨(hF _ _ t₁ t₂).1, ?_, fun e₁' e₂' => ?_⟩
    · show mulF A.ν (A.ff S (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)) (A.ff S L.ln L.ln) =
        A.ff S (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)
      rw [(hF _ _ t₁ t₂).2.2.2.2 _ _ hln hln]
      exact congrArg₂ (A.ff S) (funext (position_ln L hφ e₁)) (funext (position_ln L hfix e₂))
    · show mulF A.ν (A.ff S (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂))
          (A.ff S (intersection_update_fsHerm_neg_one Z T L.ln e₁') (intersection_update_fsHerm_neg_one Z T L.ln e₂')) =
        A.ff S (intersection_update_fsHerm_neg_one Z T φ fun w => (e₁ w).mul (e₁' w)) (intersection_update_fsHerm_neg_one Z T L.ln fun w => (e₂ w).mul (e₂' w))
      rw [(hF _ _ t₁ t₂).2.2.2.2 _ _ (hsl T e₁') (hsl T e₂')]
      exact congrArg₂ (A.ff S) (funext (position_mul L hφ e₁ e₁')) (funext (position_mul L hfix e₂ e₂'))
  · intro T e₁ e₂
    have t₁ := hsl T e₁
    have t₂ := hsl T e₂
    refine ⟨(hF _ _ t₁ t₂).1, ?_⟩
    show mulF A.ν (A.ff S L.ln L.ln) (A.ff S (intersection_update_fsHerm_neg_one Z T L.ln e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)) =
      A.ff S (intersection_update_fsHerm_neg_one Z T L.ln e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)
    rw [(hF _ _ hln hln).2.2.2.2 _ _ t₁ t₂]
    exact congrArg₂ (A.ff S) (funext (ln_position L hfix e₁)) (funext (ln_position L hfix e₂))
  · intro T w e₁ e₂ hw
    show A.ff S (intersection_update_fsHerm_neg_one Z (insert w T) L.ln e₁) (intersection_update_fsHerm_neg_one Z (insert w T) L.ln e₂) =
      mulF A.ν (A.ff S (intersection_update_fsHerm_neg_one Z {w} L.ln e₁) (intersection_update_fsHerm_neg_one Z {w} L.ln e₂))
        (A.ff S (intersection_update_fsHerm_neg_one Z T L.ln e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂))
    rw [(hF _ _ (hsl _ e₁) (hsl _ e₂)).2.2.2.2 _ _ (hsl T e₁) (hsl T e₂)]
    exact (congrArg₂ (A.ff S) (funext (position_insert L hw e₁)) (funext (position_insert L hw e₂))).symm

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

private theorem position_sph (Z T : Finset (Pl E)) (L : Lv a b Z) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (w : Pl E) (hw : w ∉ Z) : IsHecke (K2 a b w) (intersection_update_fsHerm_neg_one Z T L.ln e w) := by
  unfold intersection_update_fsHerm_neg_one
  rw [if_neg hw]
  split_ifs
  · exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w (e w)
  · exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w .one

private theorem position_Z (Z T : Finset (Pl E)) (L : Lv a b Z) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (w : Pl E) (hw : w ∈ Z) : intersection_update_fsHerm_neg_one Z T L.ln e w = L.ln w := by
  unfold intersection_update_fsHerm_neg_one
  rw [if_pos hw]

private theorem position_comm (Z T T' : Finset (Pl E)) (L : Lv a b Z) (e e' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T L.ln e w) (intersection_update_fsHerm_neg_one Z T' L.ln e' w) =
      PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T' L.ln e' w) (intersection_update_fsHerm_neg_one Z T L.ln e w) := by
  by_cases hw : w ∈ Z
  · rw [position_Z Z T L e w hw, position_Z Z T' L e' w hw]
  · exact UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 E a b w _ _ (position_sph Z T L e w hw) (position_sph Z T' L e' w hw)

private theorem position_comm_star (Z T T' : Finset (Pl E)) (L : Lv a b Z) (e e' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T L.ln e w) (lfStar (intersection_update_fsHerm_neg_one Z T' L.ln e' w)) =
      PositivityTheory.Rg.BcN.F2.mconv (lfStar (intersection_update_fsHerm_neg_one Z T' L.ln e' w)) (intersection_update_fsHerm_neg_one Z T L.ln e w) := by
  have hl := UpperTheory.Zero.ConvolutionTheory.EB.locAlg E a b Z L w
  by_cases hw : w ∈ Z
  · rw [position_Z Z T L e w hw, position_Z Z T' L e' w hw, hl.2.1]
  · exact UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 E a b w _ _ (position_sph Z T L e w hw)
      ((hl.2.2.2.2 _ (position_sph Z T' L e' w hw)).2.2)

theorem _root_.UpperTheory.Zero.ConvolutionTheory.EB.hkComm :
    UpperTheory.Zero.ConvolutionTheory.EB.HkComm := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ T T' e₁ e₂ e₁' e₂'
  have hst := UpperTheory.Zero.ConvolutionTheory.EB.positionTest E a b S Z L hZ
  have ht : ∀ (T : Finset (Pl E)) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))), IsTestP (intersection_update_fsHerm_neg_one Z T L.ln e) :=
    fun T e => (hst.2.2 L.ln hst.1).2 T e
  have hf := (UpperTheory.Zero.ConvolutionTheory.EB.ffAlg E a b l₁ l₂ D A S hS).2
  have h1 := hf _ _ (ht T e₁) (ht T e₂)
  have h2 := hf _ _ (ht T' e₁') (ht T' e₂')
  have hstar := h2.2.1
  refine ⟨?_, ?_⟩
  · show mulF A.ν (A.ff S _ _) (A.ff S _ _) = mulF A.ν (A.ff S _ _) (A.ff S _ _)
    rw [h1.2.2.2.2 _ _ (ht T' e₁') (ht T' e₂'), h2.2.2.2.2 _ _ (ht T e₁) (ht T e₂)]
    simp only [position_comm Z T T' L e₁ e₁', position_comm Z T T' L e₂ e₂']
  · show mulF A.ν (A.ff S _ _) (adjF (A.ff S _ _)) = mulF A.ν (adjF (A.ff S _ _)) (A.ff S _ _)
    rw [hstar]
    have hs := hf _ _ h2.2.2.1 h2.2.2.2.1
    rw [h1.2.2.2.2 _ _ h2.2.2.1 h2.2.2.2.1, hs.2.2.2.2 _ _ (ht T e₁) (ht T e₂)]
    simp only [position_comm_star Z T T' L e₁ e₁', position_comm_star Z T T' L e₂ e₂']

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem conv_smul' {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {ι : Type} [Fintype ι]
    (μ : Measure (H E a b)) (Φ : Matrix ι ι (H E a b → ℂ)) (c : ℂ) (f : ι → H E a b → ℂ) :
    PositivityTheory.Rg.BcB.E.conv μ Φ (c • f) = c • PositivityTheory.Rg.BcB.E.conv μ Φ f := by
  funext i x
  simp only [PositivityTheory.Rg.BcB.E.conv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  congr 1
  funext y
  ring


theorem realAlg : RealAlg := by
  intro E _ _ _ B Q _ Γ _ t v 𝔄 a₀ g s hok hK hT hs hs0
  let gg : Γ → BGen B := fun x => Sum.inr (t x)
  let X : B.Hb →L[ℂ] B.Hb := (t a₀).op
  have hmem : ∀ y : 𝔄.B, 𝔄.F y ∈ StarAlgebra.adjoin ℂ (Rd.gOps gg ∪ {X}) := by
    have hle : StarAlgebra.adjoin ℂ (Set.range 𝔄.ι) ≤ (StarAlgebra.adjoin ℂ (Rd.gOps gg ∪ {X})).comap 𝔄.F := by
      refine StarAlgebra.adjoin_le ?_
      rintro _ ⟨x, rfl⟩
      show 𝔄.F (𝔄.ι x) ∈ StarAlgebra.adjoin ℂ (Rd.gOps gg ∪ {X})
      rw [𝔄.hF]
      exact StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)
    intro y
    have hy : y ∈ StarAlgebra.adjoin ℂ (Set.range 𝔄.ι) := by
      rw [𝔄.top]
      exact StarSubalgebra.mem_top
    exact hle hy
  have hΦ : ∀ y : 𝔄.B, ∃ Φ : Matrix B.I B.I (H E B.a B.b → ℂ), IsTestM Φ ∧ IsROp B.D Φ (𝔄.F y * (t a₀).op) := fun y =>
    Rd.phiEx BlockFiniteConvolution.blkOp₀ BlockFiniteConvolution.blkWord₀ blkSum adjWords gg X (t a₀) (t a₀) (fun x => hok x) (hok a₀) rfl (hok a₀)
      ⟨𝔄.F y, hmem y⟩
  choose Φ hΦt hΦr using hΦ
  have hop : ∀ y : 𝔄.B, ∃ T : B.Hb →L[ℂ] B.Hb, IsROp B.D (Φ y) T ∧
      (∀ w : Q, T (Q.subtypeL w) = Q.subtypeL (𝔄.R (y * 𝔄.ι a₀) w)) ∧
      ∀ u, (∀ w : Q, inner ℂ (Q.subtypeL w) u = 0) → ∀ w : Q, inner ℂ (Q.subtypeL w) (T u) = 0 := by
    intro y
    have hTy : 𝔄.F y * (t a₀).op = 𝔄.F (y * 𝔄.ι a₀) := by rw [map_mul, 𝔄.hF]
    refine ⟨_, hΦr y, fun w => ?_, fun u hu w => ?_⟩
    · rw [hTy]
      exact (𝔄.hR _ w).symm
    · rw [hTy]
      have h1 : (ContinuousLinearMap.adjoint (𝔄.F (y * 𝔄.ι a₀))) (w : B.Hb) =
          Q.subtypeL (𝔄.R (star (y * 𝔄.ι a₀)) w) := by
        rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
        exact (𝔄.hR _ w).symm
      have h2 := hu (𝔄.R (star (y * 𝔄.ι a₀)) w)
      rw [← h1, ContinuousLinearMap.adjoint_inner_left] at h2
      exact h2
  have hC : ({1} ∪ Set.range 𝔄.ι : Set 𝔄.B).Countable :=
    (Set.countable_singleton _).union (Set.countable_range _)
  obtain ⟨M, sk, f, hlim, hk⟩ := PositivityTheory.Rg.BcB.E2.orthogonal_keeping_holds E B.a B.b B.D B.I Q Q.subtypeL (fun w => rfl) 𝔄.B 𝔄.R s
    (𝔄.ι a₀) ({1} ∪ Set.range 𝔄.ι) Φ g hs hs0 hC (Or.inl rfl) hΦt hop
    (fun j w => (Submodule.mem_orthogonal _ _).1 (hT.1 j) w w.2) hT.2
  refine ⟨fun k x => sk k (𝔄.ι x), f, fun x => hlim _ (Or.inr ⟨x, rfl⟩), fun k => ?_⟩
  obtain ⟨h0, hc, hne, hL, hW, hconv, horth⟩ := hk k
  have hO := fun x => BlockFiniteConvolution.blkOp₀ E B (t x) (t a₀) (hok x) (hok a₀)
  have ha : PositivityTheory.Rg.BcB.E.conv B.D.μ (t a₀).Φ (f k) = sk k (𝔄.ι a₀) • f k := by
    have h1 := hconv 1 (Or.inl rfl)
    rw [one_mul] at h1
    rw [← h1]
    refine PositivityTheory.Rg.BcB.E2.conv_eq_of_isROp B.D (hO a₀).1 (hΦt 1) ?_ (hΦr 1) hc hL
    rw [map_one, one_mul]
    exact (hO a₀).2.1
  have hx : ∀ x, PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ (f k) = sk k (𝔄.ι x) • f k := by
    intro x
    have h1 := hconv (𝔄.ι x) (Or.inr ⟨x, rfl⟩)
    have hok' := (hO x).2.2.1
    have hm := BlockFiniteConvolution.blkOp₀ E B _ _ hok' hok'
    have h2 : PositivityTheory.Rg.BcB.E.conv B.D.μ ((t x).mul (t a₀)).Φ (f k) = PositivityTheory.Rg.BcB.E.conv B.D.μ (Φ (𝔄.ι x)) (f k) := by
      refine PositivityTheory.Rg.BcB.E2.conv_eq_of_isROp B.D hm.1 (hΦt _) ?_ (hΦr _) hc hL
      rw [𝔄.hF, ← (hO x).2.2.2.1]
      exact hm.2.1
    have h3 := (UpperTheory.Zero.ConvolutionTheory.EB.convMul E B (f k) hc).1 (t x) (t a₀) (hok x) (hok a₀)
    rw [ha, conv_smul', h2, h1, map_mul] at h3
    calc PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ (f k)
        = (sk k (𝔄.ι a₀))⁻¹ • (sk k (𝔄.ι a₀)) • PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ (f k) := (inv_smul_smul₀ h0 _).symm
      _ = (sk k (𝔄.ι a₀))⁻¹ • ((sk k (𝔄.ι x) * sk k (𝔄.ι a₀)) • f k) := by rw [← h3]
      _ = sk k (𝔄.ι x) • f k := by
        rw [smul_smul]
        congr 1
        field_simp
  exact ⟨h0, ⟨hc, hne, hL, ⟨M, hW⟩, hx⟩, horth⟩

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem repAlg : RepAlg := by
  intro E _ _ _ B χa χb
  have hop := PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.blkOp₀ E B
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C ψ R h
    exact PositivityTheory.Rg.BcB.F.blkSum E B.a B.b B.D B.I C.J C.s C.c (fun j => (C.t j).Φ) (fun j => (C.t j).op)
      fun j hj => ⟨(hop _ _ (h j hj).1 (h j hj).1).1, (hop _ _ (h j hj).1 (h j hj).1).2.1⟩
  · intro t ht
    refine ⟨⟨Unit, {()}, fun _ => 1, fun _ => t⟩, ?_, ?_, ?_⟩
    · intro j _
      exact ⟨ht, rfl, le_max_left _ _, le_max_right _ _⟩
    · simp [Cmb.val]
    · simp [Cmb.op]
  · rintro ψ v R R' U h ⟨C, hC, hv, hU⟩
    exact ⟨C, fun j hj => ⟨(hC j hj).1, (hC j hj).2.1, (hC j hj).2.2.1.trans h, (hC j hj).2.2.2.trans h⟩, hv, hU⟩
  · rintro ψ ψ' v v' R R' U U' ⟨C, hC, rfl, rfl⟩ ⟨C', hC', rfl, rfl⟩
    refine ⟨⟨C.J × C'.J, C.s ×ˢ C'.s, fun p => C.c p.1 * C'.c p.2, fun p => (C.t p.1).mul (C'.t p.2)⟩, ?_, ?_, ?_⟩
    · rintro ⟨j, j'⟩ hj
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hj
      obtain ⟨o, e, hT, hr⟩ := hC j h1
      obtain ⟨o', e', hT', hr'⟩ := hC' j' h2
      refine ⟨(hop _ _ o o').2.2.1, ?_, ?_, ?_⟩
      · change mulF B.ν (C.t j).ψ (C'.t j').ψ = _
        rw [e, e']
      · change (C.t j).T + (C'.t j').T ≤ _
        linarith [B.c_nonneg]
      · change (C.t j).r + (C'.t j').r + B.c ≤ _
        linarith
    · simp only [Cmb.val]
      rw [Finset.sum_mul_sum, Finset.sum_product]
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun j' hj' => ?_
      rw [(hop _ _ (hC j hj).1 (hC' j' hj').1).2.2.2.2.2.2.1 χa χb]
      ring
    · simp only [Cmb.op]
      rw [Finset.sum_mul_sum, Finset.sum_product]
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun j' hj' => ?_
      rw [(hop _ _ (hC j hj).1 (hC' j' hj').1).2.2.2.1, smul_mul_smul_comm]

end UpperTheory.Zero.ConvolutionTheory.EB
end
end
