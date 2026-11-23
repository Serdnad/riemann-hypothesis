module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle042
public import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortColumnsDetNeZeroHilbertSamuel
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1748
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalToGlobal.IndefiniteReal.SelfDualFullLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.FunObj.FlatLast

open GlobalTheory.RootEx

section Step
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}


open Classical in
theorem stepPt_add_apply (x₀ : Matrix n n' k) (e δ : StepVar n c n' → k) (a : n ⊕ Fin c) (b : n' ⊕ Fin (c + 1)) :
    stepPt x₀ (e + δ) a b =
      stepPt x₀ e a b + if h : Free (c / 2 + 1) (a, b) ∨ Kept (a, b) then δ ⟨(a, b), h⟩ else 0 := by
  simp only [stepPt, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  split_ifs <;> ring

end Step

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}


open Classical in
def shiftVar (j₀ : Fin (G.m - 1)) (r : ℕ) (t : k) : Vars G := fun j w =>
  if j = j₀ ∧ Sum.elim (fun a : Fin (topRank G (j + 1)) => (a : ℕ) = r) (fun _ => False) w.1.1 ∧
    w.1.2.isRight = true then t else 0

theorem valuation_shiftVar_le (j₀ : Fin (G.m - 1)) (r : ℕ) {t s₀ : k} (ht : valuation k t ≤ valuation k s₀)
    (j : Fin (G.m - 1)) (w) : valuation k (shiftVar j₀ r t j w) ≤ valuation k s₀ := by
  unfold shiftVar
  split_ifs
  · exact ht
  · simp

theorem ch_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (r : ℕ) (t : k) (j : Fin (G.m - 1)) :
    ch (stepPt (x j) ((e + shiftVar j₀ r t) j)) = ch (stepPt (x j) (e j)) := by
  unfold ch
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, stepPt_add_apply]
  split_ifs <;> simp [shiftVar]

theorem rowVar_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (r : ℕ) (t : k) (j : ℕ) (s) :
    rowVar x (e + shiftVar j₀ r t) j s = rowVar x e j s := by
  unfold rowVar
  split_ifs with h
  · refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [Pi.add_apply, stepPt_add_apply]
      split_ifs <;> simp [shiftVar]
    · rfl
  · rfl

theorem colVar_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (hj₀ : (j₀ : ℕ) + 2 = G.m) (r : ℕ) (t : k)
    (j : Fin (G.m - 1)) (r' : Fin (topRank G (j + 1))) :
    colVar x (e + shiftVar j₀ r t) j r' = colVar x e j r' + if j = j₀ ∧ (r' : ℕ) = r then t else 0 := by
  unfold colVar
  rw [Pi.add_apply, stepPt_add_apply]
  congr 1
  by_cases hj : j = j₀
  · subst hj
    rw [dite_eq_left (Or.inr ⟨by rw [show G.m - 2 - (j : ℕ) = 0 by omega]; exact ⟨0, rfl⟩, rfl⟩)]
    simp [shiftVar]
  · simp [shiftVar, hj]

theorem phase_shift (x : ColArgs G) (e : Vars G) (j₀ : Fin (G.m - 1)) (hj₀ : (j₀ : ℕ) + 2 = G.m)
    (r : Fin (topRank G ((j₀ : ℕ) + 1))) (t : k) :
    phase x (e + shiftVar j₀ r t) = phase x e + rowVar x e ((j₀ : ℕ) + 1) r * t := by
  unfold phase
  have key : ∀ j : Fin (G.m - 1), (ch (stepPt (x j) ((e + shiftVar j₀ r t) j)) +
      if Even (G.m - 2 - j) then ∑ r', rowVar x (e + shiftVar j₀ r t) (j + 1) r' *
        colVar x (e + shiftVar j₀ r t) j r' else 0) =
      (ch (stepPt (x j) (e j)) + if Even (G.m - 2 - j) then ∑ r', rowVar x e (j + 1) r' * colVar x e j r' else 0) +
      if j = j₀ then rowVar x e ((j₀ : ℕ) + 1) r * t else 0 := by
    intro j
    rw [ch_shift]
    simp only [rowVar_shift, colVar_shift x e j₀ hj₀]
    by_cases hj : j = j₀
    · subst hj
      have hev : Even (G.m - 2 - (j : ℕ)) := by rw [show G.m - 2 - (j : ℕ) = 0 by omega]; exact ⟨0, rfl⟩
      rw [if_pos hev, if_pos hev, if_pos rfl]
      simp only [true_and, mul_add, Finset.sum_add_distrib, add_assoc]
      congr 2
      simp_rw [Fin.val_inj, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq']
      simp
    · simp [hj]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

variable (hs : 1 ≤ G.s)

theorem valuation_downMap_sub_le (x : ColArgs G) (e δ : Vars G) {s₀ : k}
    (hδ : ∀ j w, valuation k (δ j w) ≤ valuation k s₀) (j : ℕ) (a b) :
    valuation k (downMap hs x (e + δ) j a b - downMap hs x e j a b) ≤ valuation k s₀ := by
  classical
  unfold downMap
  split_ifs with h1 h2
  · simp only [reindex_apply, submatrix_apply, Pi.add_apply]
    rw [stepPt_add_apply, add_sub_cancel_left]
    split_ifs
    · exact hδ _ _
    · simp
  · simp
  · simp

theorem valuation_fill_sub_le (x : ColArgs G) (y : RowArgs G) (e δ : Vars G) {s₀ : k}
    (hδ : ∀ j w, valuation k (δ j w) ≤ valuation k s₀) (b : Edge) (r s) :
    valuation k ((fill hs x y (e + δ) - fill hs x y e) b r s) ≤ valuation k s₀ := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [fill, Pi.sub_apply]
    split_ifs with h
    · simp only [Matrix.sub_apply, transpose_apply, submatrix_apply]
      exact valuation_downMap_sub_le hs x e δ hδ j _ _
    · simp
  · simp only [fill, Pi.sub_apply]
    split_ifs with h
    · simp
    · simp

end GlobalTheory.FunObj.FlatLast

namespace GlobalTheory.FunObj.FlatLast
open GlobalTheory.RootEx

theorem flatTensor_lastRow_bounded : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), 2 ≤ G.m → IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 → ∀ s, valuation k (x (G.m - 1) (topLast G (G.m - 1 + 1)) s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  intro k _ _ _ _ _ _ G hs ψ ν _ ϖ e T keep g hm hϖ hψ hT
  obtain ⟨n, -, hper⟩ := GlobalTheory.MovedBound.moved_bounded_locConst G ϖ e T keep g hϖ hT
  refine ⟨n, fun x y hF => ?_⟩
  let j₀ : Fin (G.m - 1) := ⟨G.m - 2, by omega⟩
  have hj₀ : (j₀ : ℕ) + 2 = G.m := by simp only [j₀]; omega
  suffices key : ∀ r : Fin (topRank G ((j₀ : ℕ) + 1)),
      valuation k (x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) by
    have h : G.m - 1 = (j₀ : ℕ) + 1 := by omega
    rw [h]
    exact key
  intro r
  by_contra hlt
  have hu : x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r ∉ cball (1 * (ϖ ^ n)⁻¹) := by
    simpa [cball] using hlt
  obtain ⟨t, ht, hne⟩ := hψ.exists_ne_one (ϖ ^ n) hu
  set u := x ((j₀ : ℕ) + 1) (topLast G ((j₀ : ℕ) + 1 + 1)) r with hu_def
  have hrow : ∀ e' : Vars G, rowVar x e' ((j₀ : ℕ) + 1) r = u := fun e' => by
    rw [rowVar, dite_eq_right (by omega)]
  let δ : Vars G := shiftVar j₀ r (-t)
  have hδ : ∀ j w, valuation k (δ j w) ≤ valuation k ((ϖ ^ n : kˣ) : k) :=
    valuation_shiftVar_le _ _ (by simpa [cball, Valuation.map_neg] using ht)
  have hS : ∀ e' : Vars G, moved G keep g T (fill hs x y (e' + δ)) = moved G keep g T (fill hs x y e') := fun e' => by
    have := hper (fill hs x y e') (fill hs x y (e' + δ) - fill hs x y e')
      (fun b _ r s => valuation_fill_sub_le hs x y e' δ hδ b r s)
    rwa [add_sub_cancel] at this
  have hI : ∀ e' : Vars G, flatIntegrand hs ψ (moved G keep g T) x y (e' + δ) =
      (ψ (t * u) : ℂ) * flatIntegrand hs ψ (moved G keep g T) x y e' := fun e' => by
    unfold flatIntegrand
    rw [hS, phase_shift x e' j₀ hj₀ r (-t), hrow,
      show -(phase x e' + u * -t) = -phase x e' + t * u by ring, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hFeq : flatTensor hs ψ ν (moved G keep g T) x y =
      (ψ (t * u) : ℂ) * flatTensor hs ψ ν (moved G keep g T) x y := by
    have : SigmaFinite ν := inferInstance
    have : ν.IsAddRightInvariant := inferInstance
    have : (varsVol G ν).IsAddRightInvariant := by unfold varsVol; infer_instance
    unfold flatTensor
    calc ∫ e', flatIntegrand hs ψ (moved G keep g T) x y e' ∂(varsVol G ν)
        = ∫ e', flatIntegrand hs ψ (moved G keep g T) x y (e' + δ) ∂(varsVol G ν) :=
          (integral_add_right_eq_self _ δ).symm
      _ = ∫ e', (ψ (t * u) : ℂ) * flatIntegrand hs ψ (moved G keep g T) x y e' ∂(varsVol G ν) := by simp_rw [hI]
      _ = _ := integral_const_mul (ψ (t * u) : ℂ) _
  have hne' : (ψ (t * u) : ℂ) ≠ 1 := fun h => hne (Circle.ext (by simpa using h))
  have : (1 - (ψ (t * u) : ℂ)) * flatTensor hs ψ ν (moved G keep g T) x y = 0 := by
    rw [sub_mul, one_mul, ← hFeq, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact hne' (sub_eq_zero.1 h).symm
  · exact hF h

end GlobalTheory.FunObj.FlatLast
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV


theorem _root_.GlobalTheory.T.gridMovedTensor_bounded_support_locallyConstant : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, (∀ z : G.Args, moved G keep g T z ≠ 0 → ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (z b r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧ ∀ z δ : G.Args, (∀ b ∈ oppositePath G.m, ∀ r s, valuation k (δ b r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → moved G keep g T (z + δ) = moved G keep g T z := by
  first | exact @GlobalTheory.MovedBound.moved_bounded_locConst | exact GlobalTheory.MovedBound.moved_bounded_locConst | (intros; apply GlobalTheory.MovedBound.moved_bounded_locConst <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.SymImageC

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def refLev (p : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * p + 1) (fun i => 2 * (i.val + 1))

def refGroup (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | GlobalTheory.RootEx.Radical.Uni (refLev p) g.val}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun ha hb => GlobalTheory.RootEx.Radical.Uni.mul ha hb
  inv_mem' := fun ha => GlobalTheory.RootEx.Radical.Uni.inv ha

theorem N_le_refGroup {p q : ℕ} (h₁ : p ≤ q) (h₂ : q ≤ p + 1) :
    GlobalTheory.RootEx.N k n c q ≤ refGroup k n c p := by
  intro g hg r s hrs
  refine (GlobalTheory.RootEx.Radical.mem_N_iff g).1 hg r s ?_
  rcases r with r | r <;> rcases s with s | s <;>
    simp only [refLev, Sum.elim_inl, Sum.elim_inr] at hrs <;>
    simp only [GlobalTheory.RootEx.lev, Sum.elim_inl, Sum.elim_inr] <;> omega

theorem symN_le_refGroup : symN k n c ≤ refGroup k n c ((c + 1) / 2) :=
  sup_le (N_le_refGroup le_rfl (by omega)) (N_le_refGroup (by omega) (by omega))

theorem toBlocks₁₁_of_mem_symN {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) : u.val.toBlocks₁₁ = 1 := by
  have h : GlobalTheory.RootEx.Radical.Uni (refLev ((c + 1) / 2)) u.val := symN_le_refGroup hu
  ext r s
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply]
  rw [h _ _ (by simp [refLev])]
  simp [Matrix.one_apply]

theorem toBlocks₁₁_mul_embX {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) (g : GL n k) :
    (u * GlobalTheory.RootEx.embX c g).val.toBlocks₁₁ = g.val := by
  have h := toBlocks₁₁_of_mem_symN hu
  rw [Units.val_mul, GlobalTheory.RootEx.Radical.embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks u.val]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, h]
  simp

theorem toBlocks₁₁_inv_mul_embX {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) (g : GL n k) :
    ((u * GlobalTheory.RootEx.embX c g)⁻¹).val.toBlocks₁₁ = (g⁻¹).val := by
  have h := toBlocks₁₁_of_mem_symN (inv_mem hu)
  rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul, GlobalTheory.RootEx.Radical.embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (u⁻¹).val]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, h]
  simp

end GlobalTheory.FunObj.SymImageC


open GlobalTheory.FunObj.SymImageC in
theorem GlobalTheory.FunObj.SymImageC.symPr_open_bounded {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (C : Subgroup (GL (n ⊕ Fin c) k)) (hC : IsOpen (C : Set (GL (n ⊕ Fin c) k)))
    (hb : ∃ A : Set (GL (n ⊕ Fin c) k), IsCompact A ∧ (C : Set (GL (n ⊕ Fin c) k)) ⊆ A) :
    IsOpen (symPr C : Set (GL n k)) ∧ ∃ A : Set (GL n k), IsCompact A ∧ (symPr C : Set (GL n k)) ⊆ A := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  constructor
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    have ho := hC.preimage (GlobalTheory.RootEx.QuotLinear.continuous_embX (k := k) (n := n) (c := c))
    refine Filter.mem_of_superset (ho.mem_nhds (by simp [one_mem])) fun g hg => ?_
    exact ⟨1, one_mem _, by simpa using hg⟩
  · obtain ⟨A, hA, hCA⟩ := hb
    let φ : GL (n ⊕ Fin c) k → Matrix n n k × (Matrix n n k)ᵐᵒᵖ :=
      fun g => (g.val.toBlocks₁₁, MulOpposite.op (g⁻¹).val.toBlocks₁₁)
    have hbl : Continuous fun M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k => M.toBlocks₁₁ :=
      continuous_matrix fun i j => continuous_id.matrix_elem _ _
    have hφ : Continuous φ :=
      (hbl.comp Units.continuous_val).prodMk
        (MulOpposite.continuous_op.comp (hbl.comp Units.continuous_coe_inv))
    refine ⟨_, (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage (hA.image hφ),
      ?_⟩
    rintro g ⟨u, hu, h⟩
    refine ⟨_, hCA h, ?_⟩
    simp only [φ]
    rw [toBlocks₁₁_mul_embX hu, toBlocks₁₁_inv_mul_embX hu]
    rfl
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev GlobalTheory.ChiGrid
open Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField
open scoped ComplexOrder

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem UA_le_range_finE (V : HSp D) : UA D.sp.cm V.gram ≤ (finE V).range := by
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  intro x hx
  obtain ⟨b, hb⟩ := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := hπ.surjective b
  refine ⟨g, Eq.trans ?_ (congrArg Subtype.val hb)⟩
  rw [GlobalTheory.Mass.coe_swapPts, hπ g]
  rfl

theorem map_levA (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))} (hK : K ≤ UA D.sp.cm V.gram) :
    (levA V K).map (finE V) = K := by
  have h0 : (GinfC V).map (finE V) = ⊥ := (Subgroup.map_eq_bot_iff _).2 fun g hg => by
    change Formalism.UG.bc (swapAE D) (finHom V g) = 1
    rw [show finHom V g = 1 from hg, map_one]
  have h := congrArg (Subgroup.map (finE V)) (GlobalTheory.Mass.Levels.comap_finE V K)
  rw [Subgroup.map_comap_eq_self (hK.trans (UA_le_range_finE V)), Subgroup.map_sup, h0, sup_bot_eq] at h
  exact h.symm

theorem congLev_relIndex_ne_zero (V : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) :
    (congLev D.sp.cm V.gram Λ 𝔪).relIndex (congLev D.sp.cm V.gram Λ ⊤) ≠ 0 := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have ho := (congLev_open_compact V hΛ h𝔪).1
  have hc := (congLev_open_compact V hΛ (𝔪 := ⊤) top_ne_bot).2
  rw [← map_levA V (K := congLev D.sp.cm V.gram Λ ⊤) fun _ h => h.1, ← Subgroup.relIndex_comap]
  haveI := isCompact_iff_compactSpace.1 hc
  haveI : CompactSpace (levA V (congLev D.sp.cm V.gram Λ ⊤)) := this
  haveI := Subgroup.quotient_finite_of_isOpen
    (((congLev D.sp.cm V.gram Λ 𝔪).comap (finE V)).subgroupOf (levA V (congLev D.sp.cm V.gram Λ ⊤)))
    (ho.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

private theorem selfDual_isFullLattice : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
  intro V Λ hΛ
  exact Formalism.IndefR.Datum.IsSelfDualC.isFullLattice V Λ hΛ

theorem finite_cl_congLev (V : HSp D) (hV : ∀ φ : D.host.E →+* ℂ, (V.gram.map φ).PosDef)
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) : Finite (Cl D.sp.cm V.gram (congLev D.sp.cm V.gram Λ 𝔪)) := by
  have hJ := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  have hfin := Formalism.UG.Final.ClassSetFiniteL D.host.F D.host.E (Fin V.rank) D.sp.cm.sig V.gram (cm_comp D.sp.cm)
    (Matrix.ext fun i j => hJ.1 i j) hJ.2.isUnit (GlobalTheory.DefiniteQuotient.isTotDef_of_posDef V fun τ => hV _) Λ
    (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top
  have e : Formalism.UG.levelAfL D.sp.cm.sig V.gram Λ = congLev D.sp.cm V.gram Λ ⊤ := congLev_top.symm
  rw [e] at hfin
  refine class_set_finite_of_finite_index _ _ _ _ ?_ ?_ hfin
  · exact fun x hx => Subgroup.mem_subgroupOf.2 (congLev_mono le_top (Subgroup.mem_subgroupOf.1 hx))
  · rw [Subgroup.relIndex_subgroupOf (show congLev D.sp.cm V.gram Λ ⊤ ≤ UA D.sp.cm V.gram from fun _ h => h.1)]
    exact congLev_relIndex_ne_zero V hΛ h𝔪

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GlobalTheory.ChiGrid.GridData L sc)

instance finite_clPlus : Finite G.ClPlus :=
  finite_cl_congLev (Xp G) (posDef_Xp G) (selfDual_isFullLattice _ _ (isV_Xp G).sd) (G.pl.modul_ne_bot sc)

theorem finite_testIx (h : (L.ΛY 0).FG) : Finite (TestIx G) :=
  haveI := G.finite_datum h
  inferInstance

theorem exists_coords (h : (L.ΛY 0).FG) :
    ∃ n, Nonempty (Fin n ≃ GlobalTheory.FunObj.TestIx G × VVIdx (GlobalTheory.FunObj.LaP G)) := by
  haveI := finite_testIx G h
  haveI : ∀ τ, Finite (Formalism.GradedWeylDivisibility.ssIdx (Xp G).rank (Xp G).rank (LaP G τ).natW) :=
    fun τ => (Formalism.GradedWeylDivisibility.sSIdxFinite _ _ _).to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (TestIx G × VVIdx (LaP G))
  exact ⟨n, ⟨e.symm⟩⟩

end GlobalTheory.FunObj

end
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.exists_short_columns_det_ne_zero_hilbertSamuel : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → F) (δ : ℕ) (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∃ (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix ∧ S.ShortCols col ∧ (Finset.univ.filter fun k => (col k).j = S.D).card = S.deepRank s ∧ S.det c col ≠ 0 := by
  first | exact @GlobalTheory.HSShort.ChooseCols.exists_cols | exact GlobalTheory.HSShort.ChooseCols.exists_cols | (intros; apply GlobalTheory.HSShort.ChooseCols.exists_cols <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_totallyReal_even_neg_places_local_norm : ∀ (M : Type) [Field M] [NumberField M] (σ : M →+* M), σ ≠ RingHom.id M → (∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ (S : Finset (M →+* ℂ)), (∀ φ ∈ S, ComplexEmbedding.conjugate φ ∈ S) → 4 ∣ S.card → ∀ (p : ℕ) [Fact p.Prime], ∃ a : M, a ≠ 0 ∧ σ a = a ∧ (∀ φ ∈ S, (φ a).re < 0) ∧ (∀ φ : M →+* ℂ, φ ∉ S → 0 < (φ a).re) ∧ ∃ u : (AfP p ⊗[ℚ] M)ˣ, (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a := by
  first | exact @GlobalTheory.NormSign.exists_neg_even_norm_away | exact GlobalTheory.NormSign.exists_neg_even_norm_away | (intros; apply GlobalTheory.NormSign.exists_neg_even_norm_away <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.idempotent_support_hermitian_decomposition : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (S : Finset ℕ), (∀ q ∈ S, q.Prime) →
    ∀ x : GA D V, x ∈ GfC V →
    ∃ (γ : GL (Fin V.rank) D.host.E) (h k : GA D V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram ∧ h ∈ GfC V ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) ∧
      k ∈ GfC V ∧ (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) ∧
      (Formalism.IndefR.Lev.finE V x).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (Formalism.IndefR.Lev.finE V k).1 := by
  first | exact @GlobalTheory.FunObj.StdReps.exists_rep_std | exact GlobalTheory.FunObj.StdReps.exists_rep_std | (intros; apply GlobalTheory.FunObj.StdReps.exists_rep_std <;> assumption)
end
