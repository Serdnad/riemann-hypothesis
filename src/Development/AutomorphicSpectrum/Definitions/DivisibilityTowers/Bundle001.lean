module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Top

structure RootTower (Ψ : Type) [Fintype Ψ] (N : ℕ) where

  j : ℕ
  j_pos : 1 ≤ j
  j_lt : j < N

  Comp : Type
  [finC : Fintype Comp]
  [neC : Nonempty Comp]

  bad : Finset ℕ
  two_mem : 2 ∈ bad

  nu : Wt Ψ N
  nu_rat : IsRatWt nu

  M : ℕ → Comp → RootModel Ψ N

attribute [instance] RootTower.finC RootTower.neC

def scale (s : ℝ) : ℝ := Real.exp (-(s ^ 2)⁻¹)

namespace RootTower

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N) (II : IntersectionSystem)

def InS (B p : ℕ) : Prop := p.Prime ∧ (p ≤ B ∨ p ∈ T.bad)

def lamS (lam : Wt Ψ N) (s : ℝ) : Wt Ψ N := lam - s • T.nu

def vol (c : T.Comp) : ℝ :=
  (T.M 2 c).geoFun (toA (linRoot (rhoWt : Wt Ψ N) ^ dimFl Ψ N)) / flagDeg (rhoWt : Wt Ψ N)

def volT : ℝ := ∑ c, T.vol c

def PPc (B : ℕ) (c : T.Comp) (F : RP Ψ N) : ℝ := (T.M B c).PP II (toA F)

def PPt (B : ℕ) (F : RP Ψ N) : ℝ := ∑ c, T.PPc II B c F

def PBs (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℝ) : ℝ := (T.M B c).PP II (linA lam s ^ (dimFl Ψ N + 1))

def PB (B : ℕ) (lam : Wt Ψ N) : ℝ := T.PPt II B (linRoot lam ^ (dimFl Ψ N + 1))

def mbarTop (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℝ) : ℝ :=
  (T.M B c).arFun II (scale s) (linA (T.lamS lam s) s ^ (dimFl Ψ N + 1))

def mDeg (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℝ) : ℝ :=
  (T.M B c).geoFun (linA (T.lamS lam s) s ^ dimFl Ψ N)

def mbarHt (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℝ) (W : Ideal (MRing (T.M B c).ι)) : ℝ :=
  (T.M B c).ht II (scale s) (T.lamS lam s) s W

def slope (B : ℕ) (c : T.Comp) (u : Wt Ψ N) : ℝ :=
  T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)) / (((dimFl Ψ N : ℝ) + 1) * (T.vol c * flagDeg u))

def Conv : Prop := ∀ B c, (T.M B c).Converges II

def Proportional : Prop :=
  (∀ c, 0 < T.vol c) ∧ (∀ B c (F : RP Ψ N), (T.M B c).geoFun (toA F) = T.vol c * degFl F) ∧
    ∀ B B' c, (T.M B c).geoFun = (T.M B' c).geoFun

def I1 : Prop :=
  ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∀ c m, |(T.M B c).PP II (monomial m 1)| ≤ C * Real.log B

def I2 : Prop :=
  ∀ abelian₂ : ℝ, ∃ s₀ > (0 : ℝ), ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∀ c (lam : Wt Ψ N) (s : ℝ), l1 lam ≤ abelian₂ → 0 < s → s ≤ s₀ →
    Dominant (T.lamS lam s) → |T.mbarTop II B c lam s - T.PBs II B c (T.lamS lam s) s| ≤ C * s

def A1 : Prop :=
  ∀ abelian₂ : ℝ, ∃ s₀ > (0 : ℝ), ∀ B : ℕ, 2 ≤ B → ∀ c (lam : Wt Ψ N) (s : ℝ), l1 lam ≤ abelian₂ → 0 < s → s ≤ s₀ →
    Dominant (T.lamS lam s) → (T.M B c).Semipos (scale s) (T.lamS lam s) s

def ModelNefStatement : Prop := ∀ B c p, T.InS B p → ∀ mu : Wt Ψ N, Dominant mu → (T.M B c).NefAt p mu 0

def M2 : Prop :=
  ∀ B c (p : ℕ), p.Prime → ¬ T.InS B p → ∀ mu : Wt Ψ N, Dominant mu → NefThreshold T.j p mu → (T.M B c).NefAt p mu 0

def ANef : Prop := ∀ B c, (T.M B c).NefFib 0 1

def I3 : Prop :=
  ∀ abelian₂ : ℝ, ∃ s₀ > (0 : ℝ), ∀ B : ℕ, 2 ≤ B → ∀ c (lam : Wt Ψ N) (s : ℝ), l1 lam ≤ abelian₂ → 0 < s → s ≤ s₀ →
    Dominant (T.lamS lam s) → NefThreshold T.j B (T.lamS lam s) →
      (T.M B c).NefFib (T.lamS lam s) s ∧ (T.M B c).Semipos (scale s) (T.lamS lam s) s

def I5 : Prop :=
  ∀ c₀ > (0 : ℝ), ∃ θ₀ > (0 : ℝ), ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∀ c (lam : Wt Ψ N) (θ : ℝ) (s : ℚ), IsRatWt lam →
    ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (s : ℝ) = θ ^ 2 → (∀ τ, θ ≤ gap T.j lam τ) → CompactGapsGE T.j c₀ lam →
      ∀ W, (T.M B c).IsPt W → -(C * Real.log (B / (s : ℝ))) ≤ T.mbarHt II B c lam s W

def I6 : Prop :=
  ∀ c₀ > (0 : ℝ), ∃ θ₀ > (0 : ℝ), ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∀ c (lam : Wt Ψ N) (θ : ℝ) (s : ℚ), IsRatWt lam →
    ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (s : ℝ) = θ ^ 2 → (∀ τ, θ ≤ gap T.j lam τ) → CompactGapsGE T.j c₀ lam →
      ∃ F : Set (Ideal (MRing (T.M B c).ι)), IsZariskiDense (T.M B c).P F ∧
        ∀ W ∈ F, (T.M B c).IsPt W ∧ T.mbarHt II B c lam s W ≤ C * Real.log B

def I7 : Prop :=
  ∀ B c, (∀ lam : Wt Ψ N, Dominant lam → (T.M B c).NefGen lam 0) ∧ (T.M B c).NefGen 0 1 ∧ (T.M B c).EffDiff T.nu

def I8 (hh : RP Ψ N → ℝ) : Prop :=
  ∀ B : ℕ, 2 ≤ B → ∀ c τ (a b : Fin N), (b : ℕ) = a + 1 → (b : ℕ) ≠ T.j → ∀ lam : Wt Ψ N,
    T.PPc II B c (linRoot (swapWt τ a b lam) ^ (dimFl Ψ N + 1)) -
        T.vol c * hh (linRoot (swapWt τ a b lam) ^ (dimFl Ψ N + 1)) =
      -(T.PPc II B c (linRoot lam ^ (dimFl Ψ N + 1)) - T.vol c * hh (linRoot lam ^ (dimFl Ψ N + 1)))

def Prop6 (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) : Prop :=
  ∀ B₀ B : ℕ, 2 ≤ B₀ → B₀ ≤ B → ∀ c τ (k : ℕ), 1 ≤ k → k ≤ N → ∀ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N + 1 - k) →
    T.PPc II B₀ c (pk τ k * Q) = T.PPc II B c (pk τ k * Q) +
      T.vol c * ∑ p ∈ (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ T.bad), deltaTerm T.j p τ (frob p τ) k Q

def PropA : Prop :=
  ∃ Γ : Subgroup (Equiv.Perm Ψ), (∀ τ τ' : Ψ, ∃ σ ∈ Γ, σ τ = τ') ∧ ∀ σ ∈ Γ, ∀ B : ℕ, 2 ≤ B → ∀ F : RP Ψ N,
    T.PPt II B (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = T.PPt II B F

def PropF (C rd Lval : ℝ) : Prop :=
  ∃ h : ℕ → T.Comp → Ψ → ℝ,
    (∀ B : ℕ, 2 ≤ B → ∀ c τ (Q : RP Ψ N), Q.IsHomogeneous (dimFl Ψ N) →
      T.PPc II B c (pk τ 1 * Q) = h B c τ * (T.vol c * degFl Q)) ∧
    ∀ B : ℕ, 128 ≤ B → T.bad.card ≤ B → ∀ c τ, |h B c τ| ≤ C * N * bigLam B rd Lval

def VolEq : Prop := ∀ c c', T.vol c = T.vol c'

end RootTower

def I9 {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (hh : RP Ψ N → ℝ) : Prop :=
  (∀ lam : Wt Ψ N, Dominant lam → (∃ τ, ∃ a b : Fin N, (b : ℕ) = a + 1 ∧ lam τ a = lam τ b) →
      hh (linRoot lam ^ (dimFl Ψ N + 1)) = 0) ∧
    (∀ lam : Wt Ψ N, Dominant lam → 0 ≤ hh (linRoot lam ^ (dimFl Ψ N + 1))) ∧
    ∀ τ (Q : RP Ψ N), Q.IsHomogeneous (dimFl Ψ N) → hh (pk τ 1 * Q) = 0

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section

namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine mcPts)

noncomputable section

instance isPrime_span_prime (p : Nat.Primes) : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).2 (Nat.prime_iff_prime_int.1 p.2)

abbrev ZP (p : Nat.Primes) : Type := Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})

instance (p : Nat.Primes) : IsDiscreteValuationRing (ZP p) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
    (P := Ideal.span {((p : ℕ) : ℤ)})
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero) (ZP p)

variable {K : Type} {ι : K → Type} {σ : Type}

def extTo (R : Type) [CommRing R] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) : Ideal (MvPolynomial (Σ k, ι k) R) :=
  P.map (MvPolynomial.map (Int.castRingHom R))

def LocPair.IsVertOff [DecidableEq K] (T : LocPair ι ℤ σ) (P : Ideal (MvPolynomial (Σ k, ι k) ℤ))
    (S : Finset Nat.Primes) : Prop :=
  ∀ i, (∃ bf bg : K → ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (T.f i) bf ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (T.g i) bg ∧
      (fun k => (bf k : ℤ) - bg k) = T.x i - T.x' i) ∧ T.f i ∉ P ∧ T.g i ∉ P ∧
    ∀ W : Ideal (MvPolynomial (Σ k, ι k) ℤ), W.IsPrime → P ≤ W →
      GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W →
      (∀ p ∈ S, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) →
      ∃ u v : MvPolynomial (Σ k, ι k) ℤ, u ∉ W ∧ v ∉ W ∧ u * T.f i - v * T.g i ∈ P

variable [Fintype K]

def LocPair.IsIsometric (T : LocPair ι ℤ σ) (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (A A' : σ → HermLine ι) :
    Prop :=
  ∀ i, (A i).a = T.x i ∧ (A' i).a = T.x' i ∧ ∀ z ∈ mcPts P,
    ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (T.f i))‖ * (A' i).h z =
      ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (T.g i))‖ * (A i).h z

def arList (I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (l : List (HermLine ι)) : ℝ :=
  I P l.length l.get

def arNum (I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (A : σ → HermLine ι) (H : MvPolynomial σ ℝ) : ℝ :=
  ∑ μ ∈ H.support, H.coeff μ * arList I P (μ.toMultiset.map A).toList

def HasConstants (R A : Type) [CommRing R] [CommRing A] {Ω : Type} [Field Ω] [Algebra R Ω] [Algebra A Ω]
    (y : (Σ k, ι k) → Ω) : Prop :=
  ∀ c, GroundTheory.Heights₂.Heights.NumbersDVR.segreVec y c ≠ 0 → ∀ a : A,
    algebraMap A Ω a ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing R (GroundTheory.Heights₂.Heights.NumbersDVR.segreVec y) c

end

end GlobalTheory.CompanionTheory.Ar.Num
end
