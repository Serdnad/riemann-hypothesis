module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle004
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod

@[expose] public section

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private def tenPiS {J V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : J → Submodule ℂ V) : Submodule ℂ (Ten J V) where
  carrier := {x | ∀ j, x j ∈ T j}
  add_mem' {x y} hx hy j := by simpa using (T j).add_mem (hx j) (hy j)
  zero_mem' j := by simp
  smul_mem' c x hx j := by simpa using (T j).smul_mem c (hx j)

private def tenPiE {J V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : J → Submodule ℂ V) : tenPiS T ≃ₗ[ℂ] Π j, T j where
  toFun x j := ⟨x.1 j, x.2 j⟩
  invFun y := ⟨WithLp.toLp 2 fun j => (y j).1, fun j => (y j).2⟩
  map_add' x y := by ext j; simp
  map_smul' c x := by ext j; simp
  left_inv x := by ext j; simp
  right_inv y := by ext j; simp

private theorem cf_mul_sum {n : ℕ} {J : Type} (c₀ : FR n) (η : J → Wt n) (s : Finset J) (μ : Wt n) :
    cf (c₀ * ∑ j ∈ s, ex (η j)) μ = ∑ j ∈ s, cf c₀ (μ - η j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cf]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, mul_add, ((cfBasic n).2.2.2.1 _ _ 1 μ).1, ih,
      mul_comm c₀ (ex (η j)), (cfBasic n).2.2.2.2.1]

theorem UpperTheory.RealTr.tenCh :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ (J : Type) [Fintype J] [DecidableEq J] (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n), ClifMod c η → ∀ c₀, IsCh F S 1 c₀ → ∃ S' : Submodule ℂ (Ten J V), FiniteDimensional ℂ S' ∧ Stb (dg F c) S' ∧ IsCh (dg F c) S' 1 (c₀ * ∑ j, ex (η j)) := by
  intro n V _ _ F hF S hS hSt J _ _ c η hc c₀ hch
  refine ⟨tenPiS (fun _ => S), ?_, ?_, ?_⟩
  · exact Module.Finite.equiv (tenPiE (fun _ : J => S)).symm
  · intro a b x hx j
    have h : (dg F c a b x) j = F a b (x j) + ∑ k, spn c a b j k • x k := rfl
    rw [h]
    exact S.add_mem (hSt a b _ (hx j)) (S.sum_mem fun k _ => S.smul_mem _ (hx k))
  · intro μ
    have hdiag : ∀ (x : Ten J V) a j, (dg F c a a x) j = F a a (x j) + (η j a : ℂ) • x j := by
      intro x a j
      have h : (dg F c a a x) j = F a a (x j) + ∑ k, spn c a a j k • x k := rfl
      rw [h, hc.diag a]
      simp [Matrix.diagonal_apply]
    have hset : wsp (dg F c) μ ⊓ tenPiS (fun _ => S) = tenPiS (fun j => wsp F (μ - η j) ⊓ S) := by
      ext x
      constructor
      · rintro ⟨hw, hx⟩ j
        refine ⟨fun a => ?_, hx j⟩
        have h1 : (dg F c a a x) j = (μ a : ℂ) • x j := by
          have := congrArg (fun y : Ten J V => y j) (hw a)
          simpa using this
        rw [hdiag] at h1
        have h2 : F a a (x j) = (μ a : ℂ) • x j - (η j a : ℂ) • x j := eq_sub_of_add_eq h1
        rw [h2, ← sub_smul]
        simp
      · intro hx
        refine ⟨fun a => ?_, fun j => (hx j).2⟩
        ext j
        have h1 : F a a (x j) = (((μ - η j) a : ℝ) : ℂ) • x j := (hx j).1 a
        rw [hdiag, h1, ← add_smul]
        simp
    have hfin : ∀ j, FiniteDimensional ℂ ↥(wsp F (μ - η j) ⊓ S) :=
      fun j => Submodule.finiteDimensional_inf_right _ _
    have hfin' : FiniteDimensional ℂ ↥(tenPiS fun j => wsp F (μ - η j) ⊓ S) :=
      Module.Finite.equiv (tenPiE _).symm
    rw [hset, (trAdd (Ten J V) 1).2.2.2 _ hfin', LinearEquiv.finrank_eq (tenPiE _),
      Module.finrank_pi_fintype, cf_mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hch, (trAdd V 1).2.2.2 _ (hfin j)]
end
end

section

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section SlopeTestRemainingChoices

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

private theorem eu_loc (s : Bool) (a b : Fin n) {f f' : Mat n → V} (h : Set.EqOn f f' (GLs n)) :
    Set.EqOn (Eu s a b f) (Eu s a b f') (GLs n) := by
  intro x hx
  have h1 := (UpperTheory.RealTr.rdcalc n V).1 f f' h
  simp only [Eu, Pi.smul_apply, Pi.add_apply, h1 _ hx]

private theorem eu_smo (s : Bool) (a b : Fin n) {f : Mat n → V} (h : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) := by
  have h1 := ((UpperTheory.RealTr.rdcalc n V).2 f h).1
  exact ((h1 _).add ((h1 _).const_smul _)).const_smul _

private theorem rd_smul (c : ℂ) {f : Mat n → V} (h : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    Set.EqOn (Rd X (fun y => c • f y)) (fun y => c • Rd X f y) (GLs n) := by
  intro g hg
  have hd : DifferentiableAt ℝ f g :=
    (h.differentiableOn (by simp)).differentiableAt (((UpperTheory.RealTr.basic n).1).mem_nhds hg)
  have e : fderiv ℝ (fun y => c • f y) g = c • fderiv ℝ f g := (hd.hasFDerivAt.const_smul c).fderiv
  simp only [Rd, e]
  rfl

private theorem eu_smul (s : Bool) (a b : Fin n) (c : ℂ) {f : Mat n → V} (h : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Eu s a b (fun y => c • f y)) (fun y => c • Eu s a b f y) (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, rd_smul c h _ hx]
  rw [smul_comm _ c, ← smul_add, smul_comm]

private theorem epow_loc (s : Bool) (m : ℕ) (a b : Fin n) {f f' : Mat n → V} (h : Set.EqOn f f' (GLs n)) :
    Set.EqOn (Epow s m a b f) (Epow s m a b f') (GLs n) := by
  induction m generalizing a b with
  | zero =>
    intro x hx
    simp only [Epow.eq_1]
    split_ifs
    · exact h hx
    · rfl
  | succ m ih =>
    intro x hx
    simp only [Epow.eq_2, Finset.sum_apply]
    exact Finset.sum_congr rfl fun d _ => eu_loc s a d (ih d b) hx

private theorem epow_smo (s : Bool) (m : ℕ) (a b : Fin n) {f : Mat n → V} (h : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Epow s m a b f) (GLs n) := by
  induction m generalizing a b with
  | zero =>
    simp only [Epow.eq_1]
    split_ifs
    · exact h
    · exact contDiffOn_const
  | succ m ih =>
    simp only [Epow.eq_2]
    rw [Finset.sum_fn]
    exact ContDiffOn.sum fun d _ => eu_smo s a d (ih d b)

private theorem epow_smul (s : Bool) (m : ℕ) (a b : Fin n) (c : ℂ) {f : Mat n → V}
    (h : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Epow s m a b (fun y => c • f y)) (fun y => c • Epow s m a b f y) (GLs n) := by
  induction m generalizing a b with
  | zero =>
    intro x hx
    simp only [Epow.eq_1]
    split_ifs <;> simp
  | succ m ih =>
    intro x hx
    simp only [Epow.eq_2, Finset.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [eu_loc s a d (ih d b) hx]
    exact eu_smul s a d c (epow_smo s m d b h) hx

private theorem gel_loc (s : Bool) (m : ℕ) {f f' : Mat n → V} (h : Set.EqOn f f' (GLs n)) :
    Set.EqOn (gel s m f) (gel s m f') (GLs n) := by
  intro g hg
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_loc s m a a h hg

private theorem gel_smul (s : Bool) (m : ℕ) (c : ℂ) {f : Mat n → V} (h : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (gel s m (fun y => c • f y)) (fun y => c • gel s m f y) (GLs n) := by
  intro g hg
  simp only [gel, Finset.sum_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => epow_smul s m a a c h hg

end SlopeTestRemainingChoices

theorem UpperTheory.RealTr.zEig :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (χ : Inf n) (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → IsEig χ f →
      ∀ c : ℂ, (∀ x ∈ GLs n, Om (fun y => c • f y) x = cas χ • c • f x) ∧
        ∀ (w : List (Bool × ℕ)), ∀ x ∈ GLs n, zOp w (fun y => c • f y) x = (c * zVal w χ) • f x := by
  intro n V _ _ χ f hf hE c
  refine ⟨fun x hx => ?_, fun w => ?_⟩
  · simp only [Om, Pi.smul_apply, Pi.add_apply, gel_smul _ _ c hf hx, hE _ _ x hx, cas]
    module
  · induction w with
    | nil =>
      intro x hx
      simp [zOp.eq_1, zVal]
    | cons p w ih =>
      intro x hx
      simp only [zOp.eq_2]
      rw [gel_loc p.1 p.2 ih hx, gel_smul p.1 p.2 _ hf hx]
      beta_reduce
      rw [hE _ _ x hx]
      simp only [zVal, List.map_cons, List.prod_cons, smul_smul]
      ring_nf
end
end
