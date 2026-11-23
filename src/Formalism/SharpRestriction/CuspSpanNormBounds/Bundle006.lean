module

import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle031
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle026
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedMirrorLevelOperator
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle005
public import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliarySlotStates
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemVR

open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hcompl_le_primeCompl {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    hcompl (K := K) p ≤ p.primeCompl := by
  have := hp.isPrime
  unfold hcompl
  rw [Submonoid.closure_le]
  intro s hs
  exact hs.1

theorem one_mem_locR (p : Ideal (𝓞 K)) : (1 : K) ∈ locR (K := K) p :=
  ⟨1, (hcompl (K := K) p).one_mem, by rw [one_smul]; exact Submodule.mem_one.2 ⟨1, map_one _⟩⟩

theorem mul_mem_locR {p : Ideal (𝓞 K)} {x y : K} (hx : x ∈ locR (K := K) p) (hy : y ∈ locR (K := K) p) :
    x * y ∈ locR (K := K) p := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  refine ⟨s * t, (hcompl (K := K) p).mul_mem hs ht, ?_⟩
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 hsx
  obtain ⟨r', hr'⟩ := Submodule.mem_one.1 hty
  refine Submodule.mem_one.2 ⟨r * r', ?_⟩
  rw [map_mul, hr, hr', Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
  ring

theorem conjO_mem_hcompl {p : Ideal (𝓞 K)} {s : 𝓞 K} (hs : s ∈ hcompl (K := K) p) :
    conjO K s ∈ hcompl (K := K) p := by
  apply Formalism.HermitianLattices.Ext.L3.SplitA.conjO_mem_hcompl <;> assumption

theorem star_mem_locR {p : Ideal (𝓞 K)} {x : K} (hx : x ∈ locR (K := K) p) :
    star x ∈ locR (K := K) p := by
  obtain ⟨s, hs, hsx⟩ := hx
  refine ⟨conjO K s, conjO_mem_hcompl hs, ?_⟩
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 hsx
  refine Submodule.mem_one.2 ⟨conjO K r, ?_⟩
  rw [Algebra.smul_def] at hr ⊢
  have e1 : algebraMap (𝓞 K) K (conjO K r) = star (algebraMap (𝓞 K) K r) := rfl
  have e2 : algebraMap (𝓞 K) K (conjO K s) = star (algebraMap (𝓞 K) K s) := rfl
  rw [e1, e2, hr, star_mul']

theorem mem_one_of_locR {x : K} (hx : ∀ p : Ideal (𝓞 K), p.IsMaximal → x ∈ locR (K := K) p) :
    x ∈ (1 : Submodule (𝓞 K) K) := by
  let J : Ideal (𝓞 K) := (1 : Submodule (𝓞 K) K).comap (LinearMap.toSpanSingleton (𝓞 K) K x)
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hJp⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨s, hs, hsx⟩ := hx p hp
    have hsJ : s ∈ J := by
      show LinearMap.toSpanSingleton (𝓞 K) K x s ∈ (1 : Submodule (𝓞 K) K)
      rw [LinearMap.toSpanSingleton_apply]
      exact hsx
    exact hcompl_le_primeCompl hp hs (hJp hsJ)
  have h1 : (1 : 𝓞 K) ∈ J := hJ ▸ Submodule.mem_top
  change LinearMap.toSpanSingleton (𝓞 K) K x 1 ∈ (1 : Submodule (𝓞 K) K) at h1
  rwa [LinearMap.toSpanSingleton_apply, one_smul] at h1

theorem exists_local (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0) {M : Submodule (𝓞 K) K}
    (hM : M ∈ genus h (1 : Submodule (𝓞 K) K)) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    ∃ z : K, star z * z = 1 ∧ ∀ y : K, y ∈ loc (K := K) p M ↔ ∃ r ∈ locR (K := K) p, y = r * z := by
  obtain ⟨g, hg, hgM⟩ := hM.2 p hp
  refine ⟨g 1, (mem_isom_iff h1 g).1 hg, fun y => ?_⟩
  have hgx : ∀ x, g x = x * g 1 := by
    intro x
    have : g x = g (x • (1 : K)) := by simp
    rw [this, map_smul, smul_eq_mul]
  rw [← hgM, mem_gmap]
  constructor
  · intro hy
    refine ⟨g.symm y, hy, ?_⟩
    rw [← hgx, LinearEquiv.apply_symm_apply]
  · rintro ⟨r, hr, rfl⟩
    rw [← hgx, LinearEquiv.symm_apply_apply]
    exact hr

theorem norm_unit (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0) {M M' : Submodule (𝓞 K) K}
    (hM : M ∈ genus h (1 : Submodule (𝓞 K) K)) (hM' : M' ∈ genus h (1 : Submodule (𝓞 K) K)) {a : K}
    (he : M = Submodule.span (𝓞 K) {a} * M') :
    a * star a ∈ (1 : Submodule (𝓞 K) K) ∧ (a * star a)⁻¹ ∈ (1 : Submodule (𝓞 K) K) := by
  have key : ∀ p : Ideal (𝓞 K), p.IsMaximal →
      a * star a ∈ locR (K := K) p ∧ (a * star a)⁻¹ ∈ locR (K := K) p := by
    intro p hp
    obtain ⟨z, hz, hzM⟩ := exists_local h h1 hM hp
    obtain ⟨z', hz', hzM'⟩ := exists_local h h1 hM' hp
    have hl : loc (K := K) p M = Submodule.span (𝓞 K) {a} * loc (K := K) p M' := by
      rw [he, loc_mul hp]
    have hzin : z ∈ loc (K := K) p M := (hzM z).2 ⟨1, one_mem_locR p, (one_mul z).symm⟩
    rw [hl, Submodule.mem_span_singleton_mul] at hzin
    obtain ⟨m, hm, hmz⟩ := hzin
    obtain ⟨r, hr, rfl⟩ := (hzM' m).1 hm
    have haz : a * z' ∈ loc (K := K) p M := by
      rw [hl, Submodule.mem_span_singleton_mul]
      exact ⟨z', (hzM' z').2 ⟨1, one_mem_locR p, (one_mul z').symm⟩, rfl⟩
    obtain ⟨r', hr', hr'e⟩ := (hzM _).1 haz
    have hz1 : z * star z = 1 := by rw [mul_comm]; exact hz
    have hz1' : z' * star z' = 1 := by rw [mul_comm]; exact hz'
    have t1 := congrArg (fun t => t * star t) hr'e
    simp only [star_mul'] at t1
    have e1 : a * star a = r' * star r' := by
      linear_combination t1 - (a * star a) * hz1' + (r' * star r') * hz1
    have t2 := congrArg (fun t => t * star t) hmz
    simp only [star_mul'] at t2
    have e2 : a * star a * (r * star r) = 1 := by
      linear_combination t2 - (a * star a * r * star r) * hz1' + hz1
    refine ⟨e1 ▸ mul_mem_locR hr' (star_mem_locR hr'), ?_⟩
    rw [inv_eq_of_mul_eq_one_right e2]
    exact mul_mem_locR hr (star_mem_locR hr)
  exact ⟨mem_one_of_locR fun p hp => (key p hp).1, mem_one_of_locR fun p hp => (key p hp).2⟩

end Formalism.MainNotions.BridgeLemVR

end
end

section

open MeasureTheory Matrix

noncomputable section

namespace Formalism.MainNotions.S

open Formalism.QuantumDeterminants Formalism.MainNotions.S.LevR

section Val

variable {k r : ℕ}

def wbEmb (k r : ℕ) (x : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := fun p =>
  if h : r ≤ p.val ∧ p.val ≤ r + k then x ⟨p.val - r, by omega⟩ else 0

def PtRepC (B : LocBessel k r) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (B.c.re = 0 → IsPtRep B γ g) ∧ (B.c.re ≠ 0 → IsPtRepO B γ g)

def HasRep (B : LocBessel k r) (γ : Point ℂ (r + 1)) : Prop :=
  PtLastOk r (Tz k r B.z) (Tz k r B.z') γ ∧ ∃ g, PtRepC B γ g

def IsGramRef (B : LocBessel k r) (n n' : Fin (k + 1) → ℂ) (ι : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop :=
  herm (Hb k) n (wbPart k r B.z) = 0 ∧ herm (Hb k) n n = 1 ∧
  herm (Hb k) n' (wbPart k r B.z') = 0 ∧ herm (Hb k) n' n' = 1 ∧
  ∀ x y : Fin (k + 1) → ℂ, herm (Hb k) x (wbPart k r B.z') = 0 → herm (Hb k) x n' = 0 →
    herm (Hb k) y (wbPart k r B.z') = 0 → herm (Hb k) y n' = 0 →
    herm (Hb k) (ι *ᵥ x) (wbPart k r B.z) = 0 ∧ herm (Hb k) (ι *ᵥ x) n = 0 ∧
      herm (Hb k) (ι *ᵥ x) (ι *ᵥ y) = herm (Hb k) x y

def IsGramNorm (B : LocBessel k r)
    (n n' : Fin (k + 1) → ℂ) (ι : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (∃ t : ℝ, 0 < t ∧ omG k r B.z B.z' g = ((t : ℂ) * Dmin k r B.z B.z' g (Fin.last (r + 1))) • n) ∧
  (∃ t : ℝ, 0 < t ∧ omG' k r B.z B.z' g = ((t : ℂ) * star (Dmin k r B.z B.z' g (Fin.last (r + 1)))) • n') ∧
  ∀ x : Fin (k + 1) → ℂ, herm (Hb k) x (wbPart k r B.z') = 0 → herm (Hb k) x n' = 0 →
    g *ᵥ wbEmb k r x = wbEmb k r (ι *ᵥ x)

end Val

structure ValMap (k r : ℕ) where

  V : ∀ (B : LocBessel k r),
    (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (B.Wq →L[ℂ] B.Wp)) → List (ℂ × ℕ) → (B.Wq →L[ℂ] B.Wp)

  rep : LocBessel k r → List (ℂ × ℕ) → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

  n : LocBessel k r → Fin (k + 1) → ℂ
  n' : LocBessel k r → Fin (k + 1) → ℂ
  ι : LocBessel k r → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ

  ref_ok : ∀ B : LocBessel k r, 0 < k → IsGramRef B (n B) (n' B) (ι B)

  rep_ok : ∀ (B : LocBessel k r) (γ : Point ℂ (r + 1)), HasRep B γ →
    PtRepC B γ (rep B γ.1) ∧ IsGramNorm B (n B) (n' B) (ι B) (rep B γ.1)

  val : ∀ (B : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (B.Wq →L[ℂ] B.Wp)) (γ : Point ℂ (r + 1))
    (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)),
    B.c ≠ 0 → (B.c.re = 0 ∨ B.c.im = 0) → SmoothOnH (Hpk k r) F → HasRep B γ →
    IsRootMeas B γ (rep B γ.1) μR → IsOrbQuot B (rep B γ.1) μR ν → V B F γ.1 = OrbInt B F (rep B γ.1) ν

  val0 : ∀ (B : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (B.Wq →L[ℂ] B.Wp)) (γ : Point ℂ (r + 1)),
    ¬ HasRep B γ → V B F γ.1 = 0

end Formalism.MainNotions.S
end
end

section

noncomputable section

namespace Formalism.MainNotions.GapDS

open Formalism.MainNotions.PlaceDegreeData

def thrDS {n : ℕ} (ε : Fin n → Bool) : ℝ := (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1

theorem pOf_le {n : ℕ} (ε : Fin n → Bool) : pOf ε ≤ n := by
  unfold pOf
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem qOf_le {n : ℕ} (ε : Fin n → Bool) : qOf ε ≤ n := by
  unfold qOf
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem thrDS_le {n : ℕ} (ε : Fin n → Bool) : thrDS ε ≤ (n : ℝ) ^ 3 + 1 := by
  unfold thrDS
  have hp : (pOf ε : ℝ) ≤ n := by exact_mod_cast pOf_le ε
  have hq : (qOf ε : ℝ) ≤ n := by exact_mod_cast qOf_le ε
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ pOf ε := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ qOf ε := Nat.cast_nonneg _
  have : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ (n : ℝ) * n * n :=
    mul_le_mul (mul_le_mul_of_nonneg_left hp h0) hq h2 (mul_nonneg h0 h0)
  nlinarith

end Formalism.MainNotions.GapDS

end
end

section

noncomputable section

namespace Formalism.MainNotions.S.UnitaryLevelOperators

section Gauge

open Matrix MeasureTheory TensorProduct
open scoped ContDiff
open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA

end Gauge

section LevelR

open Matrix MeasureTheory TensorProduct
open scoped ContDiff
open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Parts

variable {B : Base E} {r : ℕ} (C : Ctx B r) (Γ : GCtx E r)

def lenI (B : Base E) : ℝ := sSup B.I - sInf B.I

def mid3 (B : Base E) : Set ℝ := Set.Icc (sInf B.I + lenI B / 3) (sSup B.I - lenI B / 3)

def wnormSq {n : ℕ} (wt : (Fin n → Fin 2) → B.Rho → ℂ) (x : Fin (r + 1) → ℂ) (v : (Fin n → Fin 2) → E) : ℝ :=
  ∑ s, ∑ᶠ ρ, ‖wt s ρ‖ * (B.hs (C.P ρ x (v s)) (C.P ρ x (v s))).re

end Parts

end LevelR

section Further

open Matrix MeasureTheory Filter Topology Polynomial
open scoped ContDiff
open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

def IsKFinCoefT {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ a ∈ UH (Hpk k r), ∃ b ∈ UH (Hpk k r), IsKFinCoefH σ (fun g => f (a * g * b))

section Lists

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

end Lists

def headEl (k j r' : ℕ) (h : Matrix (Fin j) (Fin j) ℂ)
    (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Matrix (Fin (2 * (j + r') + k + 1)) (Fin (2 * (j + r') + k + 1)) ℂ := fun p q =>
  if hq : q.val < j then
    (if hp : 2 * (j + r') + k + 1 - j ≤ p.val then h ⟨2 * (j + r') + k - p.val, by omega⟩ ⟨q.val, hq⟩ else 0)
  else if hq2 : q.val < 2 * r' + k + 1 + j then
    (if hp : j ≤ p.val ∧ p.val < 2 * r' + k + 1 + j then g ⟨p.val - j, by omega⟩ ⟨q.val - j, by omega⟩ else 0)
  else
    (if hp : p.val < j then (hᴴ)⁻¹ ⟨p.val, hp⟩ ⟨2 * (j + r') + k - q.val, by omega⟩ else 0)

def levOf {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ) : Lev where
  k0 := k0
  r := r
  z := L.z
  z' := L.z'
  Wp := L.Wp
  Wq := L.Wq
  π := L.π
  π' := L.π'
  μsec := μsec

def cutF {k r : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (z z' : Fin (2 * r + k + 1) → ℂ)
    (χ : ℝ → ℝ) (ε : ℝ) (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V :=
  fun g => ((χ (Gf k r z z' g / ε) : ℝ) : ℂ) • F g

def Std (D : Formalism.BasicNotions.D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS)
    (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ) (I : Set ℝ) : Prop :=
  (∀ i, L.ε i = epsSH D.R (Fin.cast (by rw [hk]) i)) ∧ L.c = cStd ∧
    IsSection (k0 + 1) D.R.rS L.z L.z' μsec ∧ IsCutS L.u L.u' I ∧
    ∃ ρ : Fin k0 → ℝ, Interlace L.u ρ ∧ Interlace L.u' ρ

abbrev Msq (s : ℕ) := Fin s → Fin s → ℂ

end Further

end Formalism.MainNotions.S.UnitaryLevelOperators
end
end
