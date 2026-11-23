module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle031
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.le_of_detIdeal_le :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ Z : Ideal P, Z.IsPrime → relIdeal z m ≤ Z → (∃ j, m j ∉ Z) →
      ringKrullDim P ≤ ringKrullDim (P ⧸ Z) + (Fintype.card ι : ℕ) →
      ∀ Q : Ideal P, Q.IsPrime → detIdeal z m ≤ Q → Z ≤ Q := by
  intro P _ _ ι _ _ z m hc Z hZ hrel hm hdim Q hQ hdet
  have hdZ : detIdeal z m ≤ Z := det_mem_of_rel P ι z m Z hZ hrel hm
  by_cases hne : Nonempty ι
  swap
  · exfalso
    have : IsEmpty ι := not_nonempty_iff.1 hne
    apply hQ.ne_top
    rw [eq_top_iff]
    refine le_trans ?_ hdet
    simp [detIdeal, Matrix.det_isEmpty]
  obtain ⟨K, hK, hKdet, hKmin⟩ := exists_least_prime_detIdeal P ι z m hc hne
  haveI := hK
  haveI := hZ
  refine le_trans ?_ (hKmin Q hQ hdet)
  have hKZ : K ≤ Z := hKmin Z hZ hdZ
  by_contra hnot
  obtain ⟨x, hxZ, hxK⟩ := Set.not_subset.1 hnot
  have hrK : relIdeal z m ≤ K :=
    le_trans (le_sup_left : relIdeal z m ≤ relIdeal z m ⊔ Ideal.span {z.det}) hKdet
  have h1 : ringKrullDim (P ⧸ Z) + 1 ≤ ringKrullDim (P ⧸ K) := by
    refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hKZ)
      (Ideal.Quotient.factor_surjective hKZ) (r := Ideal.Quotient.mk K x) ?_ ?_
    · exact mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    · simpa [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] using hxZ
  have h2 : ringKrullDim (P ⧸ K) ≤ ringKrullDim (P ⧸ relIdeal z m) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hrK) (Ideal.Quotient.factor_surjective hrK)
  have h3 := dim_relIdeal_le P ι z m hc
  have hfin : ringKrullDim (P ⧸ Z) < ⊤ := lt_of_le_of_lt (ringKrullDim_quotient_le Z) ringKrullDim_lt_top
  have hbot : ringKrullDim (P ⧸ Z) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
  have h12 := h1.trans h2
  have key : ringKrullDim (P ⧸ Z) + 1 + (Fintype.card ι : ℕ) ≤ ringKrullDim (P ⧸ Z) + (Fintype.card ι : ℕ) := by
    refine le_trans ?_ (h3.trans hdim)
    gcongr
  generalize ringKrullDim (P ⧸ Z) = d at key hfin hbot
  generalize Fintype.card ι = c at key
  induction d using WithBot.recBotCoe with
  | bot => exact hbot rfl
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => simp at hfin
    | coe d =>
      norm_cast at key
      omega
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem hk_one {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) : hk ρ I 1 = 1 :=
  (hkNorm A G M ρ I 1 hI (one_mem _)).2.1

theorem UpperTheory.V.AlgebraTools.permUnit :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (w : Equiv.Perm (Fin n)), IsUnit (resCard k : A) → IsUnit (hk ρ (iwC k n C) (pm k n w)) := by
  intro k _ _ _ _ n C A M _ _ _ ρ w hq
  have hI : HeckePair (iwC k n C) := (heckePairIwC k n C).1
  induction h : invLen w generalizing w with
  | zero =>
    rw [(lenStep n w).2.1 h, map_one, hk_one ρ _ hI]
    exact isUnit_one
  | succ m ih =>
    have hw : w ≠ 1 := by
      rintro rfl
      have h0 : invLen (1 : Equiv.Perm (Fin n)) = 0 := by
        unfold invLen
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro p _ ⟨h1, h2⟩
        exact lt_asymm h1 h2
      omega
    obtain ⟨i, j, hij, hlt⟩ := (lenStep n w).2.2 hw
    have hlen := ((lenStep n w).1 i j hij).2 hlt
    have hlt' : (Equiv.swap i j * w)⁻¹ i < (Equiv.swap i j * w)⁻¹ j := by
      simpa [_root_.mul_inv_rev, Equiv.swap_inv] using hlt
    have hm := permMul k n C A M ρ (Equiv.swap i j * w) i j hij hlt'
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul] at hm
    rw [← hm]
    exact ((simpleQuad k n C A M ρ i j hij).1 hq).mul (ih _ (by omega))
end
