module

public import GroundTheory.HeightsAndTheta.Heights.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
public import Mathlib.NumberTheory.Primorial

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.RestTerms

open MvPolynomial Matrix Real Finset

noncomputable section

def IsPart {r : ℕ} (la : Fin r → ℕ) : Prop := ∀ a b : Fin r, a ≤ b → la b ≤ la a

def shapeCells {r : ℕ} (la : Fin r → ℕ) : Finset (ℕ × ℕ) :=
  Finset.univ.biUnion fun a : Fin r => (Finset.range (la a)).image fun b => ((a : ℕ), b)

def numSYT {r : ℕ} (la : Fin r → ℕ) : ℕ :=
  Nat.card {T : shapeCells la ≃ Fin (shapeCells la).card // Monotone T}

def hookShape (k b : ℕ) : Fin (b + 1) → ℕ := fun a => if (a : ℕ) = 0 then k - b else 1

abbrev Roots (f j k : ℕ) : Type := MvPolynomial (Fin f × Fin (j + k)) ℝ

variable (f j k : ℕ)

def dimFl : ℕ := f * ((j + k) * (j + k - 1) / 2)

def nDim : ℕ := f * j * k

def psumAt (m : ℕ) (τ : Fin f) : Roots f j k := ∑ i, X (τ, i) ^ m

def lieClass (m : ℕ) (σ : Fin f × Bool) : Roots f j k :=
  if σ.2 then (-1) ^ m * ∑ b : Fin k, X (σ.1, Fin.natAdd j b) ^ m
  else ∑ a : Fin j, X (σ.1, Fin.castAdd k a) ^ m

def IsSmallBlock (bot : Bool) : Prop := (bot = true → k ≤ j) ∧ (bot = false → j ≤ k)

def smallPsum (bot : Bool) (m : ℕ) (τ : Fin f) : Roots f j k :=
  if bot then ∑ b : Fin k, X (τ, Fin.natAdd j b) ^ m
  else ∑ a : Fin j, (-X (τ, Fin.castAdd k a)) ^ m

def muClass (bot : Bool) : Roots f j k := ∑ τ, smallPsum f j k bot 1 τ

def fibClass (bot : Bool) : Roots f j k :=
  ∏ τ : Fin f, if bot then
      vandermonde (fun b : Fin k => (X (τ, Fin.natAdd j b) : Roots f j k)) *
        vandermonde (fun a : Fin j => (X (τ, Fin.castAdd k a) : Roots f j k))
    else
      vandermonde (fun a : Fin j => -(X (τ, Fin.castAdd k a) : Roots f j k)) *
        vandermonde (fun b : Fin k => (X (τ, Fin.natAdd j b) : Roots f j k))

def restPoly (bot : Bool) : Roots f j k := muClass f j k bot ^ (nDim f j k + 1) * fibClass f j k bot

def degPoly (bot : Bool) : Roots f j k := muClass f j k bot ^ nDim f j k * fibClass f j k bot

structure IsFlagIntegral (I : Roots f j k →ₗ[ℝ] ℝ) : Prop where
  kills : ∀ (m : ℕ) (τ : Fin f) (G : Roots f j k), 1 ≤ m → m ≤ dimFl f j k →
    G.IsHomogeneous (dimFl f j k - m) → I (psumAt f j k m τ * G) = 0
  ne_zero : ∃ G : Roots f j k, G.IsHomogeneous (dimFl f j k) ∧ I G ≠ 0

def IsPsumDecomp (F : Roots f j k) (Q : Fin f → ℕ → Roots f j k) : Prop :=
  (∀ τ m, 1 ≤ m → m ≤ j + k → (Q τ m).IsHomogeneous (dimFl f j k + 1 - m)) ∧
    F = ∑ τ : Fin f, ∑ m ∈ Finset.Icc 1 (j + k), psumAt f j k m τ * Q τ m

def blockAntisym : Roots f j k →ₗ[ℝ] Roots f j k :=
  ∑ w : Fin f → Equiv.Perm (Fin (j + k)),
    (((∏ τ, (Equiv.Perm.sign (w τ) : ℤ) : ℤ) : ℝ)) •
      (rename (Equiv.prodCongrRight w)).toLinearMap

def rhoMon : (Fin f × Fin (j + k)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => j + k - 1 - (v.2 : ℕ)

def ddConst : Roots f j k →ₗ[ℝ] ℝ := (lcoeff ℝ (rhoMon f j k)).comp (blockAntisym f j k)

def primesOver (P : Set ℕ) (B₀ : ℝ) : Type := {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p}

def restTerm (I : Roots f j k →ₗ[ℝ] ℝ) (σ : ℕ → ℕ → Fin f → Fin f × Bool)
    (Q : Fin f → ℕ → Roots f j k) (p : ℕ) (τ : Fin f) (m n : ℕ) : ℝ :=
  ((p : ℝ) ^ ((n + 1) * m))⁻¹ * m * I (lieClass f j k (m - 1) (σ p (n + 1) τ) * Q τ m)

def restAt (I : Roots f j k →ₗ[ℝ] ℝ) (vol : ℝ) (σ : ℕ → ℕ → Fin f → Fin f × Bool)
    (Q : Fin f → ℕ → Roots f j k) (p : ℕ) : ℝ :=
  Real.log p * vol * ∑ τ : Fin f, ∑ m ∈ Finset.Icc 2 (j + k), ∑' n : ℕ, restTerm f j k I σ Q p τ m n

def FlagIntegralProportional.Statement : Prop :=
  ∀ f j k : ℕ, 1 ≤ f → 1 ≤ j → 1 ≤ k → ∀ I : Roots f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
    ∃ c : ℝ, c ≠ 0 ∧ ∀ G : Roots f j k, G.IsHomogeneous (dimFl f j k) → I G = c * ddConst f j k G

def PrimeTail.Statement : Prop :=
  ∀ B : ℝ, 0 < B →
    Summable (fun p : {p : ℕ // p.Prime ∧ B < p} => Real.log p.1 / (p.1 : ℝ) ^ 2) ∧
      ∑' p : {p : ℕ // p.Prime ∧ B < p}, Real.log p.1 / (p.1 : ℝ) ^ 2 ≤ 2 * Real.log 4 / B

def RestBound.Statement : Prop :=
  ∀ f j k : ℕ, 1 ≤ f → 1 ≤ j → 1 ≤ k → ∀ bot : Bool, IsSmallBlock j k bot →
    ∀ I : Roots f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
    ∀ vol : ℝ, 0 < vol → ∀ P : Set ℕ, (∀ p ∈ P, p.Prime) →
    ∀ B₀ : ℝ, 4 * f * ((j + k : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ σ : ℕ → ℕ → Fin f → Fin f × Bool,
    ∀ Q : Fin f → ℕ → Roots f j k, IsPsumDecomp f j k (restPoly f j k bot) Q →
      Summable (fun p : primesOver P B₀ => restAt f j k I vol σ Q p.1) ∧
        |∑' p : primesOver P B₀, restAt f j k I vol σ Q p.1| ≤
          1.6 * ((nDim f j k : ℝ) + 1) * vol * |I (degPoly f j k bot)|

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

theorem XBound.intersectionNumber_baseChange : XBound.Statement := by
  intro r a hN
  have hN' : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast hN
  refine ⟨?_, ?_⟩
  · simp only [restX]
    push_cast
    push_cast at hN'
    nlinarith [sq_nonneg ((r : ℝ) - a)]
  · nlinarith

theorem XOverPrime.intersectionNumber_baseChange : XOverPrime.Statement := by
  intro f r a B₀ p hf hN hB hp
  have hN' : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast hN
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hX := (XBound.intersectionNumber_baseChange r a hN)
  have hX2 : (restX r a : ℝ) ≤ 3 / 2 * ((r + a : ℕ) : ℝ) ^ 2 := hX.1.trans hX.2
  have hN2 : 0 < ((r + a : ℕ) : ℝ) ^ 2 := by positivity
  have hp4 : 4 * ((r + a : ℕ) : ℝ) ^ 2 < p := by nlinarith
  have hp0 : 0 < p := lt_trans (by positivity) hp4
  rw [div_le_iff₀ hp0]
  nlinarith

theorem two_log_four_le : 2 * Real.log 4 ≤ 2.78 := by
  have := Real.log_two_lt_d9
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  nlinarith

theorem RestConstants.intersectionNumber_baseChange : RestConstants.Statement := by
  refine ⟨two_log_four_le, ?_⟩
  intro f N hf hN
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hN' : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have : (1.5 : ℝ) * f * (3 / 2 * (N : ℝ) ^ 2) * (2.78 / (4 * f * (N : ℝ) ^ 2)) =
      1.5 * (3 / 2) * 2.78 / 4 := by
    field_simp
  rw [this]
  norm_num

theorem GeometricTail.intersectionNumber_baseChange : GeometricTail.Statement := by
  intro p k hp hk
  set x : ℝ := (p ^ k)⁻¹ with hx
  have hpk : (2 : ℝ) ≤ p ^ k := by
    calc (2 : ℝ) ≤ p := hp
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := pow_le_pow_right₀ (by linarith) hk
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ 1 / 2 := by
    rw [hx]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hterm : ∀ n : ℕ, (p ^ ((n + 1) * k))⁻¹ = x * x ^ n := by
    intro n
    rw [hx, ← pow_succ', inv_pow, ← pow_mul, mul_comm k]
  have hs : Summable (fun n : ℕ => x ^ n) :=
    summable_geometric_of_lt_one hx0 (by linarith)
  refine ⟨?_, ?_⟩
  · simp_rw [hterm]
    exact hs.mul_left x
  · simp_rw [hterm]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hx0 (by linarith)]
    have h1 : (1 - x)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc x * (1 - x)⁻¹ ≤ x * 2 := mul_le_mul_of_nonneg_left h1 hx0
      _ = 2 * x := by ring

theorem exp_three_eighths_le : Real.exp (3 / 8) ≤ 1.5 := by
  have he := Real.exp_one_lt_d9
  have h8 : Real.exp (3 / 8) ^ 8 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  by_contra hlt
  push Not at hlt
  have h1 : (1.5 : ℝ) ^ 8 < Real.exp (3 / 8) ^ 8 :=
    pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
  have h2 : Real.exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
  rw [h8] at h1
  norm_num at h1 h2
  linarith

theorem ExponentialTail.intersectionNumber_baseChange : ExponentialTail.Statement := by
  intro p X hp hX hXp
  set u : ℝ := X / p with hu
  have hu0 : 0 ≤ u := by positivity
  have hu38 : u ≤ 3 / 8 := by rw [hu, div_le_iff₀ hp]; linarith
  have hA : 0 ≤ X / p ^ 2 := by positivity
  have hterm : ∀ k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) =
      X / p ^ 2 * (u ^ k * (2 / ((k + 2).factorial : ℝ))) := by
    intro k
    rw [hu, div_pow]
    field_simp
    ring
  have hfac : ∀ k : ℕ, 2 / ((k + 2).factorial : ℝ) ≤ 1 / (k.factorial : ℝ) := by
    intro k
    have h1 : (2 : ℝ) * k.factorial ≤ (k + 2).factorial := by
      have : 2 * k.factorial ≤ (k + 2).factorial := by
        rw [Nat.factorial_succ, Nat.factorial_succ]
        exact Nat.mul_le_mul (by omega) (Nat.le_mul_of_pos_left _ (by omega))
      exact_mod_cast this
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hbound : ∀ k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) ≤
      X / p ^ 2 * (u ^ k / (k.factorial : ℝ)) := by
    intro k
    rw [hterm]
    apply mul_le_mul_of_nonneg_left _ hA
    rw [div_eq_mul_one_div (u ^ k)]
    exact mul_le_mul_of_nonneg_left (hfac k) (by positivity)
  have hnn : ∀ k : ℕ, 0 ≤ 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ) := by
    intro k; positivity
  have hexp : Summable (fun k : ℕ => u ^ k / (k.factorial : ℝ)) := Real.summable_pow_div_factorial u
  have hsum : Summable (fun k : ℕ => X / p ^ 2 * (u ^ k / (k.factorial : ℝ))) := hexp.mul_left _
  have hS : Summable (fun k : ℕ => 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ)) :=
    Summable.of_nonneg_of_le hnn hbound hsum
  refine ⟨hS, ?_, ?_⟩
  · calc ∑' k : ℕ, 2 * (p ^ (k + 2))⁻¹ * X ^ (k + 1) / ((k + 2).factorial : ℝ)
        ≤ ∑' k : ℕ, X / p ^ 2 * (u ^ k / (k.factorial : ℝ)) := hS.tsum_le_tsum hbound hsum
      _ = X / p ^ 2 * Real.exp u := by
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      _ ≤ X / p ^ 2 * Real.exp (3 / 8) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu38) hA
      _ = Real.exp (3 / 8) * X / p ^ 2 := by ring
  · have := exp_three_eighths_le
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right this hA

theorem ChebyshevThetaBound.intersectionNumber_baseChange : ChebyshevThetaBound.Statement := by
  intro x hx
  set n := ⌊x⌋₊
  have hprod : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p =
      Real.log (primorial n) := by
    rw [primorial, Nat.cast_prod, Real.log_prod]
    intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    exact_mod_cast this.ne'
  rw [hprod]
  have hpos : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  calc Real.log (primorial n) ≤ Real.log ((4 : ℝ) ^ n) := by
        apply Real.log_le_log hpos
        exact_mod_cast primorial_le_four_pow n
    _ = n * Real.log 4 := by rw [Real.log_pow]
    _ ≤ x * Real.log 4 := by
        apply mul_le_mul_of_nonneg_right (Nat.floor_le hx)
        exact Real.log_nonneg (by norm_num)

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem flagIntegral_C_mul (f N : ℕ) (b : ℚ) (Φ : RootRing f N) :
    flagIntegral f N (C b * Φ) = b * flagIntegral f N Φ := by
  simp only [flagIntegral, coeff_C_mul, Finset.mul_sum, mul_assoc]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

def OtherFactorFormula.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), 2 ≤ f → 1 ≤ r → 1 ≤ a →
    ∃ C₀ : ℚ, C₀ ≠ 0 ∧
      fibreDegree f r a c =
        C₀ * (f * (r * a)).factorial / ((r * a).factorial : ℚ) ^ f *
          (numStandardTable (rectangle r a) : ℚ) ^ f ∧
      ∀ Q : ℕ → Fin f → RootRing f (r + a),
        IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q →
        ∀ (k : ℕ) (hk2 : 2 ≤ k) (hkN : k ≤ r + a) (τ τ' : Fin f), τ' ≠ τ →
          ∃ S : MvPolynomial (Fin (r + a)) ℚ,
            powerSumHom (r + a) S =
              ∑ nu ∈ partitionsOf r k,
                C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
                  aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) ∧
            restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ') =
              C₀ * k * (f * (r * a) + 1).factorial /
                  (((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
                    ((r * a).factorial : ℚ) ^ (f - 2)) *
                (numStandardTable (rectangle r a) : ℚ) ^ (f - 2) *
                symmetricGroupCharacter (rectangle r a)
                  ((k - 1) :: List.replicate (r * a - (k - 1)) 1) *
                AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1)

def SchurSignCoefficient.Statement : Prop :=
  ∀ (N r k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (nu : Fin r → ℕ) (s : ℚ), (s = 1 ∨ s = -1) →
    Antitone nu → ∑ i, nu i = k →
    ∃ S : MvPolynomial (Fin N) ℚ,
      powerSumHom N S = aeval (fun i : Fin N => C s * X i) (schur (Fin N) nu) ∧
      AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1) =
        s ^ k * if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card) / k
        else 0

def HookTableauCount.Statement : Prop :=
  ∀ r k l : ℕ, l < k → l < r → numStandardTable (hookShape r k l) = Nat.choose (k - 1) l

def RectangleTablePos.Statement : Prop :=
  ∀ r a : ℕ, 0 < numStandardTable (rectangle r a)

def HookSumBound.Statement : Prop :=
  ∀ (r a k : ℕ) (b : (Fin r → ℕ) → ℚ), 1 ≤ k →
    (∀ nu ∈ partitionsOf r k, |b nu| ≤ numStandardTable (fun i => a + nu i)) →
    ∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1), |b nu| ≤
      (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a)

end

end RestTerms

end GroundTheory.Heights₂.Heights
end
