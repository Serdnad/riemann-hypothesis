module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Values

variable {Ω : Type} [Field Ω]

omit [Fintype K] in
theorem isValueAt_add {y : (Σ k, ι k) → Ω} {s t : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (hv : IsValueAt y s z v) (hw : IsValueAt y t z w) : IsValueAt y (s + t) z (v + w) := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  obtain ⟨d', g', h', hg', hh', hy', heq', hz0', rfl⟩ := hw
  refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add (isMultiHomog_mul hg hh') ?_,
    isMultiHomog_mul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [add_comm d d']; exact isMultiHomog_mul hg' hh
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · rw [map_add (f := _), map_mul, map_mul, map_mul, heq, heq']; ring
  · rw [map_mul, map_mul]; exact mul_ne_zero hz0 hz0'
  · simp only [map_add (f := _), map_mul]
    field_simp

theorem isValueAt_intCast (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (n : ℤ) :
    IsValueAt y (n : Ω) z (n : ℂ) :=
  ⟨0, C n, 1, isMultiHomog_C_zero n, isMultiHomog_one, by simp, by simp, by simp, by simp⟩

theorem isValueAt_inv {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ}
    (hv : IsValueAt y s z v) (hs : s ≠ 0) (hv0 : v ≠ 0) : IsValueAt y s⁻¹ z v⁻¹ := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  have hgy : aeval y g ≠ 0 := by rw [heq]; exact mul_ne_zero hs hy
  have hgz : eval z (map (Int.castRingHom ℂ) g) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hv0; exact hv0 rfl
  refine ⟨d, h, g, hh, hg, hgy, ?_, hgz, by rw [inv_div]⟩
  rw [heq]
  field_simp

theorem isValueAt_pow {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ}
    (hv : IsValueAt y s z v) (n : ℕ) : IsValueAt y (s ^ n) z (v ^ n) := by
  induction n with
  | zero => simpa using isValueAt_one_self y z
  | succ n ih => rw [pow_succ, pow_succ]; exact isValueAt_mul ih hv

theorem isMultiHomog_X_single [DecidableEq K] (p : Σ k, ι k) :
    IsMultiHomog (X p : MRing ι) (fun k => if k = p.1 then 1 else 0) := by
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨a, i₀⟩ := p
  show ∑ i, (Finsupp.single (⟨a, i₀⟩ : Σ k, ι k) 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩ = if k = a then 1 else 0
  by_cases hk : k = a
  · subst hk
    rw [if_pos rfl, Finset.sum_eq_single i₀]
    · simp
    · intro i _ hi
      classical
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hi (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
    · simp
  · rw [if_neg hk]
    refine Finset.sum_eq_zero fun i _ => ?_
    classical
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hk (congrArg Sigma.fst h).symm

end Values

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Cover

variable {Ω : Type} [Field Ω]

def HasCoverBy (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (Pr : Ω → Prop) : Prop :=
  ∃ (m : ℕ) (f cc : Fin m → Ω), (∀ l, f l ∈ chartRing ℤ (segreCoord y) c) ∧
    (∀ l, cc l ∈ chartRing ℤ (segreCoord y) c) ∧ ∑ l, cc l * f l = 1 ∧ ∀ l, Pr (f l)


def zMono (z : (Σ k, ι k) → ℂ) (c : (k : K) → ι k) (a : K → ℤ) : ℂ := ∏ k, z ⟨k, c k⟩ ^ a k

end Cover

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

theorem step_le {N : ℕ} (i : Fin (N - 1)) : (i : ℕ) + 1 ≤ N := by have := i.isLt; omega

structure PlueckerData (D : ComponentData II Ψ K ι Ω E) where

  e : ∀ τ, Fin D.N → E τ
  e_indep : ∀ τ, LinearIndependent Ω (e τ)
  e_span : ∀ τ, Submodule.span Ω (Set.range (e τ)) = ⊤

  M : Ψ → Fin (D.N - 1) → ℕ
  M_ge : ∀ τ (i : Fin (D.N - 1)), Nat.choose D.N ((i : ℕ) + 1) ≤ M τ i

  bdeg : Ψ → Fin (D.N - 1) → K → ℤ

  gen : ∀ τ (i : Fin (D.N - 1)), Fin (M τ i) → Module.Dual Ω (⋀[Ω]^((i : ℕ) + 1) (E τ))
  global : ∀ τ (i : Fin (D.N - 1)) m (c : (k : K) → ι k), segreCoord D.y c ≠ 0 → ∀ v : Fin ((i : ℕ) + 1) → E τ,
    (∀ a, v a ∈ (D.W τ).lat c) →
      gen τ i m (exteriorPower.ιMulti Ω _ v) * chartMono D.y c (-bdeg τ i) ∈ chartRing ℤ (segreCoord D.y) c
  generates : ∀ τ (i : Fin (D.N - 1)) (c : (k : K) → ι k), segreCoord D.y c ≠ 0 → HasCoverBy D.y c fun f =>
    ∃ b : Fin D.N → E τ, IsFrameOver D.y (D.W τ) c f b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ A : Fin ((i : ℕ) + 1) → Fin D.N, StrictMono A → ∃ a : Fin (M τ i) → Ω,
        (∀ m, ∃ n : ℕ, f ^ n * a m ∈ chartRing ℤ (segreCoord D.y) c) ∧
        ∀ A' : Fin ((i : ℕ) + 1) → Fin D.N, StrictMono A' →
          ∑ m, a m * (gen τ i m (exteriorPower.ιMulti Ω _ (b ∘ A')) * chartMono D.y c (-bdeg τ i)) =
            if A' = A then 1 else 0

  wdeg : Ψ → K → ℤ

  ω : ∀ τ, ⋀[Ω]^D.N (E τ)
  detW : ∀ τ (c : (k : K) → ι k), segreCoord D.y c ≠ 0 → HasCoverBy D.y c fun f =>
    ∃ b : Fin D.N → E τ, IsFrameOver D.y (D.W τ) c f b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∃ u : Ω, IsUnitOn D.y c f u ∧ ω τ = (u * chartMono D.y c (-wdeg τ)) • exteriorPower.ιMulti Ω D.N b

namespace PlueckerData

variable {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D)

def ιY : K ⊕ (Ψ × Fin (D.N - 1)) → Type := Sum.elim ι fun q => Fin (Pl.M q.1 q.2)

instance instFintypeιY : ∀ k, Fintype (Pl.ιY k)
  | Sum.inl k => inferInstanceAs (Fintype (ι k))
  | Sum.inr q => inferInstanceAs (Fintype (Fin (Pl.M q.1 q.2)))

abbrev ΩY (_Pl : PlueckerData D) : Type := FractionRing (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω)

def ofΩ (x : Ω) : Pl.ΩY := algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (C x)

def gvar (τ : Ψ) (a b : Fin D.N) : Pl.ΩY :=
  algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (X (τ, a, b))


abbrev Incr (s N : ℕ) : Type := {A : Fin s → Fin N // StrictMono A}



end PlueckerData

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Frames

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ}

def headIdx {j N : ℕ} (h : j ≤ N) (a : Fin j) : Fin N := Fin.castLE h a

def tailIdx {j N : ℕ} (h : j ≤ N) (a : Fin (N - j)) : Fin N := ⟨j + a, by have := a.isLt; omega⟩

def IsAdaptedFrame (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (segreCoord y) N E) (F : Submodule Ω E)
    {j : ℕ} (hj : j ≤ N) (c : (k : K) → ι k) (f : Ω) (b : Fin N → E) : Prop :=
  IsFrameOver y W c f b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
    Submodule.span Ω (Set.range (b ∘ headIdx hj)) = F

def quotWedge (F : Submodule Ω E) {j : ℕ} (hj : j ≤ N) (b : Fin N → E) : ⋀[Ω]^(N - j) (E ⧸ F) :=
  exteriorPower.ιMulti Ω (N - j) fun a => F.mkQ (b (tailIdx hj a))

variable {y : (Σ k, ι k) → Ω} {W : ChartBundle ℤ (segreCoord y) N E} {Xo : Set ((Σ k, ι k) → ℂ)}
  {P : Ideal (MRing ι)} {n nc : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)} {χ : Fin nc → SncChart P n Bd}


open Classical in
def gramAt (hm : HermMetric y W Xo χ) (b : Fin N → E) (z : (Σ k, ι k) → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  if hl : ∃ l, InFrameDomain y (hm.chart l) (hm.fr l) z then
    if hS : ∃ S : Matrix (Fin N) (Fin N) Ω, ∀ q, b q = ∑ p, S p q • hm.b hl.choose p then
      (Matrix.of fun p q => valAt y (hS.choose p q) z)ᴴ * hm.gram hl.choose z *
        Matrix.of fun p q => valAt y (hS.choose p q) z
    else 0
  else 0

def quotNormSq {j : ℕ} (hj : j ≤ N) (G : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  G.det.re / (G.submatrix (headIdx hj) (headIdx hj)).det.re

end Frames

section Main

theorem ComponentData.j_le_N {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω]
    [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    (D : ComponentData II Ψ K ι Ω E) : D.j ≤ D.N :=
  D.j_le.trans (Nat.sub_le _ _)

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

structure HodgeData (D : ComponentData II Ψ K ι Ω E) where

  F : ∀ τ, Submodule Ω (E τ)

  aMu : K → ℤ

  Λ : PiTensorProduct Ω fun τ => ⋀[Ω]^(D.N - D.j) (E τ ⧸ F τ)

  locally : ∀ c : (k : K) → ι k, segreCoord D.y c ≠ 0 →
    ∃ (m : ℕ) (f cc : Fin m → Ω), (∀ l, f l ∈ chartRing ℤ (segreCoord D.y) c) ∧
      (∀ l, cc l ∈ chartRing ℤ (segreCoord D.y) c) ∧ ∑ l, cc l * f l = 1 ∧
      ∀ l, ∃ b : ∀ τ, Fin D.N → E τ,
        (∀ τ, IsAdaptedFrame D.y (D.W τ) (F τ) D.j_le_N c (f l) (b τ)) ∧
        ∃ u : Ω, IsUnitOn D.y c (f l) u ∧
          Λ = (u * chartMono D.y c aMu) • PiTensorProduct.tprod Ω fun τ => quotWedge (F τ) D.j_le_N (b τ)

variable {D : ComponentData II Ψ K ι Ω E}

structure MuFrameAt (H : HodgeData D) (z : (Σ k, ι k) → ℂ) where
  c : (k : K) → ι k
  f : Ω
  inDom : InFrameDomain D.y c f z
  b : ∀ τ, Fin D.N → E τ
  adapted : ∀ τ, IsAdaptedFrame D.y (D.W τ) (H.F τ) D.j_le_N c f (b τ)
  u : Ω
  unit : IsUnitOn D.y c f u
  eq : H.Λ = (u * chartMono D.y c H.aMu) • PiTensorProduct.tprod Ω fun τ => quotWedge (H.F τ) D.j_le_N (b τ)

def MuFrameAt.norm {H : HodgeData D} {z : (Σ k, ι k) → ℂ} (d : MuFrameAt H z) : ℝ :=
  ‖valAt D.y d.u z‖ * (∏ k, ‖z ⟨k, d.c k⟩‖ ^ H.aMu k) *
    ∏ τ, Real.sqrt (quotNormSq D.j_le_N (gramAt (D.h τ) (d.b τ) z))


open Classical in
def muMetric (H : HodgeData D) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if h : Nonempty (MuFrameAt H z) then h.some.norm else 0

def muLine (H : HodgeData D) : HermLine ι := hermOfFun ι H.aMu (muMetric H)

def phMu (H : HodgeData D) (z : (Σ k, ι k) → ℂ) : ℝ := Real.log ((muLine H).h z)

end Main

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
