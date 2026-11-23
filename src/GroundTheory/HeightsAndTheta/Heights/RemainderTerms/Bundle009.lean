module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
public import GroundTheory.HeightsAndTheta.Heights.Bundle001
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

theorem RestPrimeBoundOfFactor.proof (h₁ : RestInnerTsumBound.Statement)
    (h₂ : RestKSumBound.Statement) : RestPrimeBoundOfFactor.Statement := by
  intro f r a c B₀ hf hr ha hB Q hT s e he p hp hpB
  set Y : ℝ := ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| with hY
  set X : ℝ := (restX r a : ℝ) with hX
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hX0 : 0 ≤ X := by rw [hX]; unfold restX; positivity
  have hN : 2 ≤ r + a := by omega
  have hXp : X ≤ 3 / 8 * (p : ℝ) := by
    have := XOverPrime.intersectionNumber_baseChange f r a B₀ p hf hN hB hpB
    rw [div_le_iff₀ hp0] at this
    linarith
  have hY0 : 0 ≤ Y := by positivity

  have hterm : ∀ τ : Fin f, ∀ k ∈ Finset.Icc 2 (r + a),
      |∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
        ((e p (n + 1) τ k * restTerm f (r + a) Q k τ
          (smallPowerSum f r a c (k - 1) (s p (n + 1) τ)) : ℚ) : ℝ)| ≤
        (Y * X ^ (k - 1) / (k.factorial : ℝ)) * (2 * ((p : ℝ) ^ k)⁻¹) := by
    intro τ k hk
    rw [Finset.mem_Icc] at hk
    refine (h₁ (p : ℝ) k _ _ hp2 (by omega) ?_).2
    intro n
    have hb := hT k hk.1 hk.2 τ (s p (n + 1) τ)
    have habs : |e p (n + 1) τ k * restTerm f (r + a) Q k τ
        (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| =
        |restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| := by
      rw [abs_mul]
      rcases he p (n + 1) τ k with h | h <;> simp [h]
    rw [← Rat.cast_abs, habs]
    calc ((|restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| : ℚ) : ℝ)
        ≤ ((((f * (r * a) + 1 : ℕ) : ℚ) * |fibreDegree f r a c| * restX r a ^ (k - 1) /
            (k.factorial : ℚ) : ℚ) : ℝ) := Rat.cast_le.mpr hb
      _ = Y * X ^ (k - 1) / (k.factorial : ℝ) := by
        rw [hY, hX]; push_cast; ring
  have hsumk := h₂ (p : ℝ) X (r + a) hp0 hX0 hXp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  unfold restPrimeModel
  rw [abs_mul, abs_of_nonneg hlog]
  calc Real.log p * |∑ τ : Fin f, ∑ k ∈ Finset.Icc 2 (r + a), ∑' n : ℕ,
        ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
          ((e p (n + 1) τ k * restTerm f (r + a) Q k τ
            (smallPowerSum f r a c (k - 1) (s p (n + 1) τ)) : ℚ) : ℝ)|
      ≤ Real.log p * ∑ τ : Fin f, ∑ k ∈ Finset.Icc 2 (r + a),
          (Y * X ^ (k - 1) / (k.factorial : ℝ)) * (2 * ((p : ℝ) ^ k)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hlog
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        exact hterm τ k hk
    _ = Real.log p * ((f : ℝ) * (Y * ∑ k ∈ Finset.Icc 2 (r + a),
          2 * ((p : ℝ) ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ Real.log p * ((f : ℝ) * (Y * (1.5 * X / (p : ℝ) ^ 2))) := by
        gcongr
    _ = 1.5 * (f : ℝ) * X * (Real.log p / (p : ℝ) ^ 2) * Y := by ring
    _ = 1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| := by
        rw [hY, hX]; ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem RestInnerTsumBound.proof : RestInnerTsumBound.Statement := by
  intro p k c M hp hk hc
  obtain ⟨hsum, hle⟩ := GeometricTail.intersectionNumber_baseChange p k hp hk
  have hM : 0 ≤ M := (abs_nonneg (c 0)).trans (hc 0)
  have hnn : ∀ n : ℕ, 0 ≤ (p ^ ((n + 1) * k))⁻¹ := fun n => by
    have : (0 : ℝ) ≤ p := by linarith
    positivity
  have hbound : ∀ n : ℕ, ‖(p ^ ((n + 1) * k))⁻¹ * c n‖ ≤ (p ^ ((n + 1) * k))⁻¹ * M := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn n)]
    exact mul_le_mul_of_nonneg_left (hc n) (hnn n)
  have hsumM : Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * M) := hsum.mul_right M
  have hS : Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * c n) :=
    Summable.of_norm_bounded hsumM hbound
  refine ⟨hS, ?_⟩
  calc |∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * c n|
      = ‖∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * c n‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖(p ^ ((n + 1) * k))⁻¹ * c n‖ := norm_tsum_le_tsum_norm hS.norm
    _ ≤ ∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * M := hS.norm.tsum_le_tsum hbound hsumM
    _ = (∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹) * M := tsum_mul_right
    _ ≤ (2 * (p ^ k)⁻¹) * M := mul_le_mul_of_nonneg_right hle hM
    _ = M * (2 * (p ^ k)⁻¹) := mul_comm _ _

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def SchStrictAntiSplit.Statement : Prop :=
  ∀ (r n : ℕ) (d : Fin r → ℕ), StrictAnti d → ∑ i, d i = r * (r - 1) / 2 + n →
    (∀ i : Fin r, r - 1 - (i : ℕ) ≤ d i) ∧
      (fun i : Fin r => d i - (r - 1 - (i : ℕ))) ∈ partitionsOf r n

def SchAltPartitionExpansion.Statement : Prop :=
  ∀ (r n : ℕ) (P : MvPolynomial (Fin r) ℚ), Comb.IsAlt P →
    P.IsHomogeneous (r * (r - 1) / 2 + n) →
    P = ∑ lam ∈ partitionsOf r n,
      C (AddMonoidAlgebra.coeff P (Finsupp.equivFunOnFinite.symm fun i : Fin r => lam i + (r - 1 - (i : ℕ)))) *
        (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) * schur (Fin r) lam)

def rootOfUnity (k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / k)

def rootOfUnityPoint (N k : ℕ) : Fin N → ℂ :=
  fun i => if (i : ℕ) < k then rootOfUnity k ^ (i : ℕ) else 0

def rootOfUnityJTMatrix (k : ℕ) {r : ℕ} (nu : Fin r → ℕ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j =>
    if 0 ≤ (nu i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) ∧
        (k : ℤ) ∣ (nu i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) then 1 else 0

def SchProdOneSubRootsOfUnity.Statement : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∏ i ∈ range k, (1 - Polynomial.C (rootOfUnity k ^ i) * Polynomial.X) =
      (1 - Polynomial.X ^ k : Polynomial ℂ)

def SchCompleteGenerating.Statement : Prop :=
  ∀ (N : ℕ) (y : Fin N → ℂ) (d : ℕ),
    ∑ c ∈ range (d + 1), (∏ i : Fin N, (1 - Polynomial.C (y i) * Polynomial.X)).coeff c *
      aeval y (hsymm (Fin N) ℚ (d - c)) = if d = 0 then 1 else 0

def SchCompleteAtRootsOfUnity.Statement : Prop :=
  ∀ N k d : ℕ, 1 ≤ k → k ≤ N →
    aeval (rootOfUnityPoint N k) (hsymm (Fin N) ℚ d) = if k ∣ d then 1 else 0

def SchPowerSumAtRootsOfUnity.Statement : Prop :=
  ∀ N k j : ℕ, 1 ≤ k → k ≤ N → 1 ≤ j →
    aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ j) = if k ∣ j then (k : ℂ) else 0

def SchPowerSumHomWeighted.Statement : Prop :=
  ∀ (N d : ℕ) (S : MvPolynomial (Fin N) ℚ),
    S.IsWeightedHomogeneous (fun i : Fin N => (i : ℕ) + 1) d → (powerSumHom N S).IsHomogeneous d

def SchWeightedPreimage.Statement : Prop :=
  ∀ (N k : ℕ) (P : MvPolynomial (Fin N) ℚ), P.IsSymmetric → P.IsHomogeneous k →
    ∃ S, powerSumHom N S = P ∧ S.IsWeightedHomogeneous (fun i : Fin N => (i : ℕ) + 1) k

def SchEvalPowerSumHom.Statement : Prop :=
  ∀ (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (S : MvPolynomial (Fin N) ℚ),
    S.IsWeightedHomogeneous (fun i : Fin N => (i : ℕ) + 1) k →
      aeval (rootOfUnityPoint N k) (powerSumHom N S) =
        (k : ℂ) * ((AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1) : ℚ) : ℂ)

def SchSchurHomogeneous.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r : ℕ) (lam : Fin r → ℕ),
    (schur σ lam).IsHomogeneous (∑ i, lam i)

def SchSchurRowsToK.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r k : ℕ) (nu : Fin r → ℕ), Antitone nu →
    ∑ i, nu i = k →
    schur σ nu = schur σ (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0)

def SchSchurEvalMatrix.Statement : Prop :=
  ∀ (N k r : ℕ) (nu : Fin r → ℕ), 1 ≤ k → k ≤ N →
    aeval (rootOfUnityPoint N k) (schur (Fin N) nu) = (rootOfUnityJTMatrix k nu).det

def SchRootOfUnityBialternant.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k →
    (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det =
      (rootOfUnityJTMatrix k nu).det * vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ))

def SchRootOfUnityRowsPerm.Statement : Prop :=
  ∀ (k : ℕ) (l : Fin k → ℕ) (π : Equiv.Perm (Fin k)), 1 ≤ k →
    (∀ i, l i % k = k - 1 - (π i : ℕ)) →
      (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * l i)).det =
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
          (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).det

def SchRootOfUnityRowsEq.Statement : Prop :=
  ∀ (k : ℕ) (l : Fin k → ℕ) (i i' : Fin k), i ≠ i' → l i % k = l i' % k →
    (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * l i)).det = 0

def SchHookResidues.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k → Antitone nu → ∑ i, nu i = k →
    (∀ i : Fin k, (i : ℕ) ≠ 0 → nu i ≤ 1) →
    ∃ π : Equiv.Perm (Fin k), (∀ i, (nu i + (k - 1 - (i : ℕ))) % k = k - 1 - (π i : ℕ)) ∧
      ((Equiv.Perm.sign π : ℤ)) =
        (-1) ^ (univ.filter fun i : Fin k => (i : ℕ) ≠ 0 ∧ nu i = 1).card

def SchResidueCount.Statement : Prop :=
  ∀ (k : ℕ) (l : Fin k → ℕ), (∀ i, l i < 2 * k) → Function.Injective (fun i => l i % k) →
    ∑ i, l i = k * (k - 1) / 2 + k * (univ.filter fun i => k ≤ l i).card

def SchNonHookResidues.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k → Antitone nu → ∑ i, nu i = k →
    ¬ (∀ i : Fin k, (i : ℕ) ≠ 0 → nu i ≤ 1) →
    ∃ i i' : Fin k, i ≠ i' ∧ (nu i + (k - 1 - (i : ℕ))) % k = (nu i' + (k - 1 - (i' : ℕ))) % k

def SchRootOfUnityVandermondeNe.Statement : Prop :=
  ∀ k : ℕ, 1 ≤ k → vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) ≠ 0

def SchJTMatrixDetAtRoots.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k → Antitone nu → ∑ i, nu i = k →
    (rootOfUnityJTMatrix k nu).det =
      if ∀ i : Fin k, (i : ℕ) ≠ 0 → nu i ≤ 1 then
        (-1) ^ (univ.filter fun i : Fin k => (i : ℕ) ≠ 0 ∧ nu i = 1).card else 0

def SchSchurAtRootsOfUnity.Statement : Prop :=
  ∀ (N r k : ℕ) (nu : Fin r → ℕ), 1 ≤ k → k ≤ N → Antitone nu → ∑ i, nu i = k →
    aeval (rootOfUnityPoint N k) (schur (Fin N) nu) =
      if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
        (-1) ^ (univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card else 0

def smallBlockPlace (r a : ℕ) (c : SmallBlock) : Fin r ⊕ Fin a → Fin 1 × Fin (r + a) :=
  Sum.elim (yIndex 1 r a c 0) (zIndex 1 r a c 0)

def smallBlockOf (r a : ℕ) : SmallBlock → Fin (r + a) → Fin r ⊕ Fin a
  | .last, p =>
    if h : (p : ℕ) < a then Sum.inr ⟨p, h⟩ else Sum.inl ⟨(p : ℕ) - a, by have := p.isLt; omega⟩
  | .first, p =>
    if h : (p : ℕ) < r then Sum.inl ⟨p, h⟩ else Sum.inr ⟨(p : ℕ) - r, by have := p.isLt; omega⟩

def SchAevalSignedRename.Statement : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (s : ℚ) (g : ι → κ)
    (d : ℕ) (P : MvPolynomial ι ℚ), P.IsHomogeneous d →
    aeval (fun i => C s * (X (g i) : MvPolynomial κ ℚ)) P = C (s ^ d) * rename g P

def SchAntisymmetrizePlace.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock) (Q : MvPolynomial (Fin r ⊕ Fin a) ℚ),
    antisymmetrize 1 (r + a) (rename (smallBlockPlace r a c) Q) =
      rename (smallBlockPlace r a c) (antisym Q)

def SchSmallBlockProduct.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock) (lam : Fin r → ℕ),
    aeval (yRoot 1 r a c 0) (schur (Fin r) lam) * vandermondeOf (yRoot 1 r a c 0) *
        vandermondeOf (zRoot 1 r a c 0) =
      C (c.sign ^ (∑ i, lam i + r * (r - 1) / 2)) *
        rename (smallBlockPlace r a c)
          (rename Sum.inl (alternant fun i : Fin r => lam i + (r - 1 - (i : ℕ))) *
            rename Sum.inr (alternant fun j : Fin a => a - 1 - (j : ℕ)))

def SchAlternantRenamePlace.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock) (v : Fin r ⊕ Fin a → ℕ),
    rename (smallBlockPlace r a c) (alternant v) =
      rename (fun p : Fin (r + a) => ((0 : Fin 1), p)) (alternant (v ∘ smallBlockOf r a c))

def SchConcatExponent.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock), ∃ τ : Equiv.Perm (Fin (r + a)),
    ∀ lam : Fin r → ℕ, (∀ i, a ≤ lam i) →
      (Sum.elim (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) (fun j : Fin a => a - 1 - (j : ℕ)))
          ∘ smallBlockOf r a c =
        (fun p : Fin (r + a) =>
          Schur.padPartition (r + a) (fun i : Fin r => lam i - a) p + (r + a - 1 - (p : ℕ))) ∘ τ

def SchConcatAlternant.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock), ∃ s : ℚ, (s = 1 ∨ s = -1) ∧
    ∀ lam : Fin r → ℕ, (∀ i, a ≤ lam i) →
      rename (smallBlockPlace r a c)
          (alternant (Sum.elim (fun i : Fin r => lam i + (r - 1 - (i : ℕ)))
            (fun j : Fin a => a - 1 - (j : ℕ)))) =
        C s * rename (fun p : Fin (r + a) => ((0 : Fin 1), p))
          (vandermondeOf (fun p : Fin (r + a) => (X p : MvPolynomial (Fin (r + a)) ℚ)) *
            schur (Fin (r + a)) (fun i : Fin r => lam i - a))

def SchConcatAlternantZero.Statement : Prop :=
  ∀ (r a : ℕ) (lam : Fin r → ℕ), Antitone lam → ¬ (∀ i, a ≤ lam i) →
    alternant (Sum.elim (fun i : Fin r => lam i + (r - 1 - (i : ℕ)))
      (fun j : Fin a => a - 1 - (j : ℕ))) = 0

def SchBlockVandermondeOne.Statement : Prop :=
  ∀ N : ℕ, blockVandermonde 1 N =
    rename (fun p : Fin N => ((0 : Fin 1), p))
      (vandermondeOf (fun p : Fin N => (X p : MvPolynomial (Fin N) ℚ)))

def SchAlternantHomogeneous.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (e : ι → ℕ), (alternant e).IsHomogeneous (∑ i, e i)

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace FlagEq

variable {f N : ℕ}

def permSign (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) : ℤ :=
  ∏ τ, ((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ)

def stairExp (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) : Fin f × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => N - 1 - ((w v.1).symm v.2 : ℕ)

def rho (f N : ℕ) : Fin f × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => N - 1 - (v.2 : ℕ)

def stairConst (f N : ℕ) : ℝ := (∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ)) ^ f

theorem stairExp_one : stairExp f N 1 = rho f N := by
  ext v; simp [stairExp, rho, Equiv.Perm.one_def]

theorem permSign_one : permSign f N 1 = 1 := by simp [permSign]

theorem permSign_inv (w : Fin f → Equiv.Perm (Fin N)) : permSign f N w⁻¹ = permSign f N w := by
  simp [permSign, Equiv.Perm.sign_inv]

theorem permSign_mul (u w : Fin f → Equiv.Perm (Fin N)) :
    permSign f N (u * w) = permSign f N u * permSign f N w := by
  simp [permSign, Equiv.Perm.sign_mul, prod_mul_distrib]

theorem permSign_mul_self (u : Fin f → Equiv.Perm (Fin N)) :
    permSign f N u * permSign f N u = 1 := by
  rw [permSign, ← prod_mul_distrib]
  exact prod_eq_one fun τ _ => by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

theorem stairConst_pos : 0 < stairConst f N :=
  pow_pos (prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _) _

theorem coeff_rename_prodCongrRight {R : Type*} [CommSemiring R] (w : Fin f → Equiv.Perm (Fin N))
    (P : MvPolynomial (Fin f × Fin N) R) (d : Fin f × Fin N →₀ ℕ) :
    AddMonoidAlgebra.coeff (rename (Equiv.prodCongrRight w) P) d =
      AddMonoidAlgebra.coeff P (Finsupp.equivFunOnFinite.symm fun v => d (Equiv.prodCongrRight w v)) := by
  rw [← coeff_rename_mapDomain (Equiv.prodCongrRight w) (Equiv.injective _) P]
  congr 1
  ext v
  obtain ⟨u, rfl⟩ := (Equiv.prodCongrRight w).surjective v
  rw [Finsupp.mapDomain_apply_of_injective (Equiv.injective _)]
  simp

theorem coeff_rho_antisym {R : Type*} [CommRing R] (P : MvPolynomial (Fin f × Fin N) R) :
    AddMonoidAlgebra.coeff (∑ w : Fin f → Equiv.Perm (Fin N),
        ((permSign f N w : ℤ) : R) • rename (Equiv.prodCongrRight w) P) (rho f N) =
      ∑ w, ((permSign f N w : ℤ) : R) * AddMonoidAlgebra.coeff P (stairExp f N w) := by
  rw [coeff_sum]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ (fun w => ?_)
  rw [MvPolynomial.coeff_smul, smul_eq_mul, coeff_rename_prodCongrRight, Equiv.inv_apply, permSign_inv]
  congr 2

theorem blockVandermonde_eq_sum (f N : ℕ) :
    blockVandermonde f N = ∑ w : Fin f → Equiv.Perm (Fin N),
      ((permSign f N w : ℤ) : ℚ) • monomial (stairExp f N w) (1 : ℚ) := by
  simp only [blockVandermonde, Comb.vandermondeOf_eq_det, Matrix.det_apply', Matrix.of_apply]
  rw [prod_univ_sum, Fintype.piFinset_univ]
  refine sum_congr rfl fun w _ => ?_
  rw [prod_mul_distrib, smul_eq_C_mul, monomial_eq, C_1, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  congr 1
  · simp [permSign]
  · refine prod_congr rfl fun τ _ => ?_
    symm
    rw [← Equiv.prod_comp (w τ)]
    simp [stairExp]

theorem coeff_blockVandermonde (α : Fin f × Fin N →₀ ℕ) :
    AddMonoidAlgebra.coeff (blockVandermonde f N) α =
      ∑ w, ((permSign f N w : ℤ) : ℚ) * if stairExp f N w = α then 1 else 0 := by
  rw [blockVandermonde_eq_sum, coeff_sum]
  simp only [MvPolynomial.coeff_smul, coeff_monomial, smul_eq_mul]

theorem eq_one_of_stairExp_eq (w : Fin f → Equiv.Perm (Fin N)) (h : stairExp f N w = rho f N) :
    w = 1 := by
  funext τ
  ext i
  have h1 := DFunLike.congr_fun h (τ, w τ i)
  simp [stairExp, rho] at h1
  have := (w τ i).isLt
  have := i.isLt
  simp only [Pi.one_apply, Equiv.Perm.coe_one, id_eq]
  omega

theorem prod_factorial_stairExp (w : Fin f → Equiv.Perm (Fin N)) :
    (stairExp f N w).prod (fun _ e => (e.factorial : ℝ)) = stairConst f N := by
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Fintype.prod_prod_type]
  have h : ∀ τ, ∏ i : Fin N, ((stairExp f N w (τ, i)).factorial : ℝ) =
      ∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ) := by
    intro τ
    simp only [stairExp, Finsupp.coe_equivFunOnFinite_symm]
    exact Equiv.prod_comp (w τ).symm (fun i : Fin N => ((N - 1 - (i : ℕ)).factorial : ℝ))
  rw [prod_congr rfl (fun τ _ => h τ), prod_const, card_univ, Fintype.card_fin, stairConst]

theorem rho_degree (f N : ℕ) : (rho f N).degree = f * (N * (N - 1) / 2) := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  simp only [rho, Finsupp.coe_equivFunOnFinite_symm, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N]
  have h := sum_range_reflect (fun i => i) N
  rw [h, sum_range_id]

end FlagEq

end

end GroundTheory.Heights₂.Heights.RestTerms
end
