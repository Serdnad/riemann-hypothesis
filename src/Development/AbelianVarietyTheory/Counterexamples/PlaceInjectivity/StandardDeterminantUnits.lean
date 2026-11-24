module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnimodularLatticeLocalConjSymm
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StandardDeterminantUnit

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Survey.StandardDeterminantUnits

open Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

omit [StarRing E] in
theorem val_le_one_of_intAt {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : IntAt P a) : P.valuation E a ≤ 1 := by
  obtain ⟨r, s, hs, hsa⟩ := h
  have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 :=
    (P.valuation_eq_one_iff_notMem (K := E)).2 hs
  have h2 : P.valuation E (algebraMap (𝓞 E) E r) ≤ 1 := P.valuation_le_one r
  rw [← hsa, map_mul, h1, one_mul] at h2
  exact h2

private theorem single_one_mem_stdAt (P : HeightOneSpectrum (𝓞 E)) (j : Fin n) :
    (Pi.single j (1 : E) : Sp E n) ∈ stdAt E n P := by
  rw [stdAt, mem_localization_standardLattice]
  intro i
  by_cases hij : i = j
  · subst hij
    simpa using IntAt.coe P (1 : 𝓞 E)
  · simpa [Pi.single_apply, hij] using IntAt.coe P (0 : 𝓞 E)

theorem val_det_le_one {P : HeightOneSpectrum (𝓞 E)} (g : Sp E n →ₗ[E] Sp E n)
    (hg : ∀ x ∈ stdAt E n P, g x ∈ stdAt E n P) : P.valuation E (LinearMap.det g) ≤ 1 := by

  rw [← LinearMap.det_toMatrix', ← Valuation.mem_integer_iff, Matrix.det_apply']
  refine Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _)
    (Subring.prod_mem _ fun i _ => ?_)
  rw [Valuation.mem_integer_iff, LinearMap.toMatrix'_apply]
  have hx := hg _ (single_one_mem_stdAt P i)
  rw [stdAt, mem_localization_standardLattice] at hx
  exact val_le_one_of_intAt (hx (σ i))

theorem mem_at_conj {N : Submodule (𝓞 E) (Sp E n)} (hl : N.FG) (hu : IsUnimodular (hStd E n) N)
    (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ localization₂ (conjPrime₂ P).asIdeal N ↔ ∀ y ∈ localization₂ P.asIdeal N, IntAt (conjPrime₂ P) (hStd E n y x) := by
  first | exact _root_.GlobalTheory.GO.UniExt.mem_localization_conj_iff | exact @_root_.GlobalTheory.GO.UniExt.mem_localization_conj_iff | apply _root_.GlobalTheory.GO.UniExt.mem_localization_conj_iff <;> assumption

end Generic

end GlobalTheory.Survey.StandardDeterminantUnits
