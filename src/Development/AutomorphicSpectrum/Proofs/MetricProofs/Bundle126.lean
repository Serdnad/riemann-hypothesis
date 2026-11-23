module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle117
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Blocks

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem blkF_eq_none_iff (Ψ : Type) (p q : ℕ) (K₀ : Type) (r : Ψ × Fin (p + q)) :
    blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2 := by
  unfold blkF
  split_ifs with h <;> simp [h]

theorem stepOf_injective (Ψ : Type) (p q : ℕ) : Function.Injective (stepOf Ψ p q) := by
  rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
  have hi := i.2
  have hi' := i'.2
  by_cases h₁ : (i : ℕ) < p <;> by_cases h₂ : (i' : ℕ) < p
  · simp only [stepOf, dite_eq_left h₁, dite_eq_left h₂] at h
    have e₁ : τ = τ' := Sum.inl.inj (congrArg Sigma.fst h)
    have e₂ := congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
    exact Prod.ext e₁ (Fin.ext e₂)
  · simp only [stepOf, dite_eq_left h₁, dite_eq_right h₂] at h
    exact absurd (congrArg Sigma.fst h) (by simp)
  · simp only [stepOf, dite_eq_right h₁, dite_eq_left h₂] at h
    exact absurd (congrArg Sigma.fst h) (by simp)
  · simp only [stepOf, dite_eq_right h₁, dite_eq_right h₂] at h
    have e₁ : τ = τ' := Sum.inr.inj (congrArg Sigma.fst h)
    have e₂ : (i : ℕ) - p = (i' : ℕ) - p := congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
    exact Prod.ext e₁ (Fin.ext (by show (i : ℕ) = (i' : ℕ); omega))

theorem blkF_inj (Ψ : Type) (p q : ℕ) (K₀ : Type) (r r' : Ψ × Fin (p + q)) (k : K₀ ⊕ StepIx Ψ p q)
    (h : blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = some k)
    (h' : blkF (Ψ := Ψ) (p := p) (q := q) K₀ r' = some k) : r = r' := by
  unfold blkF at h h'
  split_ifs at h h'
  apply stepOf_injective Ψ p q
  have e := (Option.some.inj h).trans (Option.some.inj h').symm
  exact Sum.inr.inj e

theorem fromBlocks_isBlockDiag {R : Type} [CommRing R] (p q : ℕ) (A : Matrix (Fin q) (Fin q) R)
    (B : Matrix (Fin p) (Fin p) R) :
    IsBlockDiag p ((Matrix.fromBlocks A 0 0 B).submatrix (blockEquiv p q).symm (blockEquiv p q).symm) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
  obtain ⟨y, rfl⟩ := (blockEquiv p q).surjective b
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases x with x | x <;> rcases y with y | y
  · exfalso
    apply hab
    have hx := x.2
    have hy := y.2
    show ((x : ℕ) < _ ↔ (y : ℕ) < _)
    omega
  · rfl
  · rfl
  · exfalso
    apply hab
    show (q + (x : ℕ) < _ ↔ q + (y : ℕ) < _)
    omega

theorem gMat_isBlockDiag (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ) :
    IsBlockDiag p (gMat p q Ω τ) :=
  fromBlocks_isBlockDiag p q (genU Ω (rk Ψ p q) (.inr τ)) (genU Ω (rk Ψ p q) (.inl τ))

theorem blocks_main : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (K₀ : Type),
    (∀ r, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2) ∧
    (∀ r r' k, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = some k →
      blkF (Ψ := Ψ) (p := p) (q := q) K₀ r' = some k → r = r') ∧
    ∀ τ : Ψ, IsBlockDiag p (gMat p q Ω τ) :=
  fun Ψ _ p q Ω _ K₀ => ⟨blkF_eq_none_iff Ψ p q K₀, blkF_inj Ψ p q K₀, gMat_isBlockDiag Ψ p q Ω⟩

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Blocks
end
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.blkF_properStep_injective_blockDiag :
    ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (K₀ : Type),
      (∀ r, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2) ∧
      (∀ r r' k, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = some k →
        blkF (Ψ := Ψ) (p := p) (q := q) K₀ r' = some k → r = r') ∧
      ∀ τ : Ψ, IsBlockDiag p (gMat p q Ω τ) := by
  intro Ψ _ p q Ω _ K₀
  have stepOf_injective : Function.Injective (stepOf (Ψ := Ψ) (p := p) (q := q)) := by
    rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
    have hi := i.2
    have hi' := i'.2
    by_cases h₁ : (i : ℕ) < p <;> by_cases h₂ : (i' : ℕ) < p
    · simp only [stepOf, dite_eq_left h₁, dite_eq_left h₂] at h
      have e₁ : τ = τ' := Sum.inl.inj (congrArg Sigma.fst h)
      have e₂ := congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
      exact Prod.ext e₁ (Fin.ext e₂)
    · simp only [stepOf, dite_eq_left h₁, dite_eq_right h₂] at h
      exact absurd (congrArg Sigma.fst h) (by simp)
    · simp only [stepOf, dite_eq_right h₁, dite_eq_left h₂] at h
      exact absurd (congrArg Sigma.fst h) (by simp)
    · simp only [stepOf, dite_eq_right h₁, dite_eq_right h₂] at h
      have e₁ : τ = τ' := Sum.inr.inj (congrArg Sigma.fst h)
      have e₂ : (i : ℕ) - p = (i' : ℕ) - p :=
        congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
      exact Prod.ext e₁ (Fin.ext (by show (i : ℕ) = (i' : ℕ); omega))
  have fromBlocks_isBlockDiag {R : Type} [CommRing R] (A : Matrix (Fin q) (Fin q) R)
      (B : Matrix (Fin p) (Fin p) R) :
      IsBlockDiag p ((Matrix.fromBlocks A 0 0 B).submatrix
        (blockEquiv p q).symm (blockEquiv p q).symm) := by
    intro a b hab
    obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
    obtain ⟨y, rfl⟩ := (blockEquiv p q).surjective b
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases x with x | x <;> rcases y with y | y
    · exfalso
      apply hab
      have hx := x.2
      have hy := y.2
      show ((x : ℕ) < _ ↔ (y : ℕ) < _)
      omega
    · rfl
    · rfl
    · exfalso
      apply hab
      show (q + (x : ℕ) < _ ↔ q + (y : ℕ) < _)
      omega
  refine ⟨?_, ?_, ?_⟩
  · intro r
    unfold blkF
    split_ifs with h <;> simp [h]
  · intro r r' k h h'
    unfold blkF at h h'
    split_ifs at h h'
    apply stepOf_injective
    have e := (Option.some.inj h).trans (Option.some.inj h').symm
    exact Sum.inr.inj e
  · intro τ
    exact fromBlocks_isBlockDiag
      (genU Ω (rk Ψ p q) (.inr τ)) (genU Ω (rk Ψ p q) (.inl τ))
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}

def tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    Matrix (Fin (p + q)) (Fin (p + q)) Ω :=
  (Matrix.fromBlocks (Ts (.inr τ)) 0 0 (Ts (.inl τ))).submatrix (blockEquiv p q).symm (blockEquiv p q).symm

def cMin (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (t : StepIx Ψ p q)
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) (I : Finset (Fin (p + q))) : Ω :=
  if e : I.card = (t.2 : ℕ) + 1 then ((aExt C t.1).submatrix J (I.orderEmbOfFin e)).det else 0


open Classical in
def bExt (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (s : Ψ ⊕ Ψ) : Matrix (Fin (p + q)) (Fin (n s)) Ω :=
  fun a j => ∑ l, if posOf p q s l = a then B s l j else 0

def bMin (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (t : StepIx Ψ p q)
    (I : Finset (Fin (p + q))) (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) : Ω :=
  if e : I.card = (t.2 : ℕ) + 1 then ((bExt B t.1).submatrix (I.orderEmbOfFin e) J).det else 0


variable (p q) in
def fullT (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) : StepIx Ψ p q := ⟨s, ⟨rk Ψ p q s - 1, by omega⟩⟩

theorem fullT_base (K₀ : Type) (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) (r : Ψ × Fin (p + q)) :
    blkF (Ψ := Ψ) (p := p) (q := q) K₀ r ≠ some (.inr (fullT p q s h)) := by
  intro hr
  unfold blkF at hr
  split_ifs at hr with hp
  obtain ⟨h1, h2⟩ := hp
  simp only [Option.some.injEq, Sum.inr.injEq] at hr
  unfold stepOf fullT at hr
  have hv := r.2.isLt
  split_ifs at hr with hlt
  · rw [Sigma.mk.inj_iff] at hr
    obtain ⟨hs, hx⟩ := hr
    subst hs
    have hx' := congrArg Fin.val (eq_of_heq hx)
    simp [rk] at hx' h
    omega
  · rw [Sigma.mk.inj_iff] at hr
    obtain ⟨hs, hx⟩ := hr
    subst hs
    have hx' := congrArg Fin.val (eq_of_heq hx)
    simp [rk] at hx' h
    omega

def baseFull (K₀ : Type) (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) :
    NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀) :=
  ⟨.inr (fullT p q s h), fullT_base K₀ s h⟩

def baseInl {K₀ : Type} (k : K₀) : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀) :=
  ⟨.inl k, fun r => by
    classical
    unfold blkF
    split_ifs <;> simp⟩

variable {K₀ : Type} {J₀ : K₀ → Type}

def xcOf [Fintype K₀] (x₀ : (Σ k, J₀ k) → Ω)
    (c : ∀ k : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀),
      baseIdx (idx (p := p) (q := q) J₀ n) (blkF (Ψ := Ψ) (p := p) (q := q) K₀) k) : Ω :=
  ∏ k, x₀ ⟨k, c (baseInl k)⟩

def rowsOf (c : ∀ k : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀),
      baseIdx (idx (p := p) (q := q) J₀ n) (blkF (Ψ := Ψ) (p := p) (q := q) K₀) k)
    (s : Ψ ⊕ Ψ) : Fin (rk Ψ p q s) → Fin (n s) :=
  fun a => c (baseFull K₀ s (by have := a.2; omega)) (Fin.cast (by have := a.2; show _ = rk Ψ p q s - 1 + 1; omega) a)

def zOf (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (c : ∀ k : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀),
      baseIdx (idx (p := p) (q := q) J₀ n) (blkF (Ψ := Ψ) (p := p) (q := q) K₀) k)
    (s : Ψ ⊕ Ψ) : Ω :=
  ((A s).submatrix (rowsOf c s) id).det

theorem xb_full [Fintype Ψ] [Fintype K₀] [∀ k, Fintype (J₀ k)] (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (x₀ : (Σ k, J₀ k) → Ω) (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) (J : Fin (rk Ψ p q s) → Fin (n s)) :
    xb A x₀ ⟨baseFull K₀ s h, fun a => J (Fin.cast (by show _ = rk Ψ p q s; have := a.2; show rk Ψ p q s - 1 + 1 = _; omega) a)⟩ =
      ((A s).submatrix J id).det := by
  simp only [xb, baseFull, xv]
  have e : rk Ψ p q s - 1 + 1 = rk Ψ p q s := by omega
  rw [← Matrix.det_submatrix_equiv_self (finCongr e) ((A s).submatrix J id)]
  rfl

theorem xb_rowsOf [Fintype Ψ] [Fintype K₀] [∀ k, Fintype (J₀ k)] (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (x₀ : (Σ k, J₀ k) → Ω)
    (c : ∀ k : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀),
      baseIdx (idx (p := p) (q := q) J₀ n) (blkF (Ψ := Ψ) (p := p) (q := q) K₀) k)
    (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) :
    xb A x₀ ⟨baseFull K₀ s h, c (baseFull K₀ s h)⟩ = zOf A c s :=
  xb_full A x₀ s h (rowsOf c s)

theorem det_mem_subring {ι : Type} [Fintype ι] [DecidableEq ι] (R : Subring Ω) (M : Matrix ι ι Ω)
    (h : ∀ a b, M a b ∈ R) : M.det ∈ R := by
  rw [Matrix.det_apply]
  refine R.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact R.zsmul_mem (R.prod_mem fun i _ => h _ _) _


open Classical in
def sMin (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (t : StepIx Ψ p q)
    (I : Finset (Fin (p + q))) (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) : Ω :=
  if StrictMono J then bMin B t I J else 0

private theorem card_filter_fin_Ico (N lo hi : ℕ) (hh : hi ≤ N) :
    (Finset.univ.filter (fun a : Fin N => lo ≤ (a : ℕ) ∧ (a : ℕ) < hi)).card = hi - lo := by
  rw [← Nat.card_Ico lo hi]
  apply Finset.card_bij (fun (a : Fin N) _ => (a : ℕ))
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_Ico]
    omega
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro b hb
    simp only [Finset.mem_Ico] at hb
    exact ⟨⟨b, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, rfl⟩

theorem card_stepCols (r : Ψ × Fin (p + q)) :
    (stepCols (p + q) p r.2).card = ((stepOf Ψ p q r).2 : ℕ) + 1 := by
  have hv := r.2.isLt
  unfold stepCols
  by_cases hc : (r.2 : ℕ) < p
  · have hs : stepOf Ψ p q r = ⟨Sum.inl r.1, ⟨r.2, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dite_eq_left hc]
    have hc' : (r.2 : ℕ) + 1 ≤ p := hc
    rw [hs]
    simp only [if_pos hc']
    rw [card_filter_fin_Ico _ _ _ (by omega)]
    omega
  · have hs : stepOf Ψ p q r = ⟨Sum.inr r.1, ⟨r.2 - p, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dite_eq_right hc]
    have hc' : ¬ ((r.2 : ℕ) + 1 ≤ p) := by omega
    rw [hs]
    simp only [if_neg hc']
    have := card_filter_fin_Ico (p + q) 0 ((r.2 : ℕ) + 1 - p) (by omega)
    simp only [Nat.zero_le, true_and] at this
    rw [this]
    omega

theorem stepRows_pos (r : Ψ × Fin (p + q)) {I : Finset (Fin (p + q))} (h : IsStepRows (p + q) p r.2 I) :
    ∀ a ∈ I, ∃ l, posOf p q (stepOf Ψ p q r).1 l = a := by
  intro a ha
  obtain ⟨-, hsub⟩ := h
  have hmem := hsub ha
  have hv := a.isLt
  by_cases hc : (r.2 : ℕ) < p
  · have hs : stepOf Ψ p q r = ⟨Sum.inl r.1, ⟨r.2, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dite_eq_left hc]
    have hc' : (r.2 : ℕ) + 1 ≤ p := hc
    rw [if_pos hc'] at hmem
    simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [hs]
    refine ⟨⟨a - q, by simp [rk]; omega⟩, ?_⟩
    simp only [posOf, wEmb]
    ext
    simp only
    omega
  · have hs : stepOf Ψ p q r = ⟨Sum.inr r.1, ⟨r.2 - p, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dite_eq_right hc]
    have hc' : ¬ ((r.2 : ℕ) + 1 ≤ p) := by omega
    rw [if_neg hc'] at hmem
    simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [hs]
    refine ⟨⟨a, by simp [rk]; omega⟩, ?_⟩
    simp only [posOf, omEmb]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase

theorem det_genU (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) : (genU Ω r s).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [genU]
  · intro l k hlk
    have hlk' : l < k := hlk
    have h1 : ¬ k < l := not_lt.2 hlk'.le
    have h2 : l ≠ k := hlk'.ne
    simp [genU, h1, h2]

theorem det_map_mul_submatrix {Ω L : Type} [Field Ω] [Field L] (f : Ω →+* L) {n m r : ℕ} (hm : m = r) (h : m ≤ r)
    (A : Matrix (Fin n) (Fin r) Ω) (U : Matrix (Fin r) (Fin r) L) (hU : U.det = 1) (J : Fin m → Fin n) :
    ((A.map f * U).submatrix J (Fin.castLE h)).det = f ((A.submatrix J (Fin.castLE h)).det) := by
  subst hm
  have hc : (Fin.castLE h : Fin m → Fin m) = id := by
    funext i
    rfl
  rw [hc, RingHom.map_det]
  have : (A.map f * U).submatrix J id = (f.mapMatrix (A.submatrix J id)) * U := by
    ext a b
    simp [Matrix.mul_apply]
  rw [this, Matrix.det_mul, hU, mul_one]

variable {Ψ : Type} {p q : ℕ}

theorem full_of_noBlock (K₀ : Type) (t : StepIx Ψ p q)
    (h : ∀ r, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r ≠ some (.inr t)) : (t.2 : ℕ) + 1 = rk Ψ p q t.1 := by
  obtain ⟨s, i⟩ := t
  rcases s with τ | τ
  · have hi : (i : ℕ) < p := i.2
    by_contra hne
    have hne' : (i : ℕ) + 1 ≠ p := hne
    refine h (τ, ⟨i, by omega⟩) ?_
    have hp : IsProperStep (p + q) p (⟨i, by omega⟩ : Fin (p + q)) := ⟨hne', by
      show (i : ℕ) + 1 ≠ p + q
      omega⟩
    simp only [blkF, if_pos hp, stepOf]
    simp [hi]
    rfl
  · have hi : (i : ℕ) < q := i.2
    by_contra hne
    have hne' : (i : ℕ) + 1 ≠ q := hne
    refine h (τ, ⟨p + i, by omega⟩) ?_
    have hp : IsProperStep (p + q) p (⟨p + i, by omega⟩ : Fin (p + q)) := ⟨by
      show p + (i : ℕ) + 1 ≠ p
      omega, by
      show p + (i : ℕ) + 1 ≠ p + q
      omega⟩
    simp only [blkF, if_pos hp, stepOf]
    simp
    rfl

theorem basePart_yv : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ)
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type)
    [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), ∀ r,
    basePart (blkF (Ψ := Ψ) (p := p) (q := q) K₀) (yv A x₀) r =
      algebraMap Ω (GenField Ω (rk Ψ p q)) (xb A x₀ r) := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ r
  obtain ⟨⟨k, hk⟩, i⟩ := r
  rcases k with k | t
  · rfl
  · exact det_map_mul_submatrix (algebraMap Ω (GenField Ω (rk Ψ p q))) (full_of_noBlock K₀ t hk) t.2.2 (A t.1)
      (genU Ω (rk Ψ p q) t.1) (det_genU Ω _ _) i

end GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase
end
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.mixed_energy_uniform_bound : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X), IsPotential A Θ → IsPosPot A Θ → ∀ (P : Fin e → LocPot X) (C : ℝ), (∀ i, IsPotential A (P i)) → ∃ CE : ℝ, ∀ f : Fin e → X → ℝ, (∀ i, A.Smooth (f i)) → (∀ i, IsPsh A (P i + LocPot.ofFun (f i))) → (∀ i, ∀ x ∈ R.Yo, |f i x| ≤ C + C * Real.log (R.r x)) → (∀ i, ∀ x ∈ R.Yo, f i x ≤ C) → GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A R.Yo R.r (fun i => P i + LocPot.ofFun (f i)) CE := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.tailLogProducts | exact GlobalTheory.CompanionTheory.Ar.Giv.tailLogProducts | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.tailLogProducts <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem pFl_isArithVar : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N →
    IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) :=
  @PositivityTheory.Xgp.t_c_fl_arith

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.log_resolution_fubini_study_positive : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D), (∀ A : HermLine ι, IsSmoothHerm A → IsPotential R.A (potOf R A)) ∧ IsSmoothHerm (fsHerm ι fun _ => 1) ∧ IsPosPot R.A (potOf R (fsHerm ι fun _ => 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential | exact GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential <;> assumption)
end
