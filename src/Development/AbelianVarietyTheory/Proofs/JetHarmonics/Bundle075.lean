module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle029
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CircleIntegralInvSubEqZeroOfOutside
import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle002
public import Formalism.PeriodIntegrals.Bundle024
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle064
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle066
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle020
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle017
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FamilyDegreeRatio

theorem gap_lam {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    (H : Num k r lam u b bv ga h q0) (a c : Fin (2 * r + k + 1)) (hac : a < c) :
    100 * ((q0 : ℝ) + 1) ≤ lam a - lam c := by
  obtain ⟨hk, ⟨hanti, -⟩, -, -, -, hcl, hnd, -, -, hga, hh, -, hq1, hq2, -⟩ := H
  by_cases hc : c.val + 1 < k
  · linarith [hga a c hac hc]
  by_cases ha : a.val + 1 < k
  ·
    have hp : k - 1 < 2 * r + k + 1 := by omega
    have hq : k < 2 * r + k + 1 := by omega
    have hpq : PI.BesselPeriodGGP.eps48 k r ⟨k - 1, hp⟩ ≠ PI.BesselPeriodGGP.eps48 k r ⟨k, hq⟩ := by
      have h1 : ¬ (k < k - 1) := by omega
      have h2 : (k - (k - 1)) % 2 = 1 := by omega
      simp [PI.BesselPeriodGGP.eps48, h1, h2]
    have hgpq := hh _ _ hpq
    have ⟨p1, p2⟩ := hnd ⟨k - 1, hp⟩ (by show k ≤ k - 1 + 1; omega)
    have ⟨q1, q2⟩ := hnd ⟨k, hq⟩ (by show k ≤ k + 1; omega)
    have habs : |lam ⟨k - 1, hp⟩ - lam ⟨k, hq⟩| ≤ bv := abs_le.mpr ⟨by linarith, by linarith⟩
    have h1 := (hcl a ha).1
    have h2 := (hnd c (by omega)).2
    linarith
  ·
    have hac' : a.val < c.val := hac
    have hd : a.val + 1 < 2 * r + k + 1 := by have := c.isLt; omega
    have had : a < ⟨a.val + 1, hd⟩ := by rw [Fin.lt_def]; simp
    have hdc : (⟨a.val + 1, hd⟩ : Fin (2 * r + k + 1)) ≤ c := by rw [Fin.le_iff_val_le_val]; simp; omega
    have hne : PI.BesselPeriodGGP.eps48 k r a ≠ PI.BesselPeriodGGP.eps48 k r ⟨a.val + 1, hd⟩ := by
      have h1 : ¬ (a.val < k - 1) := by omega
      have h2 : ¬ (a.val + 1 < k - 1) := by omega
      rcases Nat.mod_two_eq_zero_or_one (a.val - (k - 1)) with h3 | h3
      · have h4 : (a.val + 1 - (k - 1)) % 2 = 1 := by omega
        simp [PI.BesselPeriodGGP.eps48, h1, h2, h3, h4]
      · have h4 : (a.val + 1 - (k - 1)) % 2 = 0 := by omega
        simp [PI.BesselPeriodGGP.eps48, h1, h2, h3, h4]
    have hg := hh _ _ hne
    have hlt := hanti had
    have hle := hanti.antitone hdc
    rw [abs_of_pos (by linarith)] at hg
    linarith

theorem abs_coord_le_of_lOneNorm_le {n : ℕ} {ν : Fin n → ℤ} {q : ℕ} (hν : n1 ν ≤ q) (a : Fin n) : |(ν a : ℝ)| ≤ q := by
  have h1 : (ν a).natAbs ≤ n1 ν :=
    Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ a)
  have h2 : |(ν a : ℝ)| = ((ν a).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h2]
  exact_mod_cast h1.trans hν

theorem degree_ratios : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → 0 < Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) ∧ (∀ I : Finset (Fin (2 * r + k + 1)), Formalism.QuantumDeterminants.fdegHC (fun a => lam a + ((ν + eZ I) a : ℝ)) ≤ ((2 * r + k + 1) : ℝ) ^ I.card * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ))) ∧ ∀ s, Formalism.QuantumDeterminants.fdegHC (fun a => lam a + ((ν - Pi.single s (1 : ℤ) : Fin (2 * r + k + 1) → ℤ) a : ℝ)) / Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) = ∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - 1 - (lam t + (ν t : ℝ))| / |lam s + (ν s : ℝ) - (lam t + (ν t : ℝ))| := by
  intro k r lam u b bv ga h q0 H ν hν
  have hgl := fun a c (hac : a < c) => gap_lam H a c hac
  have hνb := fun a => abs_le.mp (abs_coord_le_of_lOneNorm_le hν a)
  have hint := H.2.1.2
  have hq : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
  have hgap : ∀ a c : Fin (2 * r + k + 1), a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
    intro a c hac
    have := hgl a c hac
    have := hνb a
    have := hνb c
    linarith
  have hanti : StrictAnti (fun a => lam a + (ν a : ℝ)) := fun a c hac => by
    have := hgap a c hac
    simp only
    linarith
  have hinj := hanti.injective
  have hZ : ∀ a c, ∃ m : ℤ, (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) = (m : ℝ) := by
    intro a c
    obtain ⟨m1, hm1⟩ := hint a
    obtain ⟨m2, hm2⟩ := hint c
    exact ⟨m1 - m2 + ν a - ν c, by push_cast; linarith⟩
  have hpos : 0 < Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) := Formalism.QuantumDeterminants.formal_degree_pos_holds _ _ hinj
  refine ⟨hpos, ?_, ?_⟩
  · intro I
    have hb := (Formalism.HermitianLatticeCounting.P.degree_set_cardinality_bound (2 * r + k + 1) (fun a => lam a + (ν a : ℝ)) I hanti hZ hgap).2
    have hfun : (fun a => lam a + (((ν + eZ I) a : ℤ) : ℝ)) =
        (fun a => (lam a + (ν a : ℝ)) + if a ∈ I then 1 else 0) := by
      funext a
      simp only [Pi.add_apply, eZ]
      split_ifs <;> push_cast <;> ring
    rw [hfun]
    rw [div_le_iff₀ hpos] at hb
    push_cast at hb
    exact hb
  · intro s
    have hfun : (fun a => lam a + (((ν - Pi.single s (1 : ℤ) : Fin (2 * r + k + 1) → ℤ) a : ℤ) : ℝ)) =
        (fun a => lam a + (ν a : ℝ)) + Pi.single s (-1 : ℝ) := by
      funext a
      by_cases has : a = s
      · subst has
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Int.cast_sub, Int.cast_one]
        ring
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne has, sub_zero, add_zero]
    rw [hfun, GlobalTheory.CompareIterDegree.fdeg_ratio_abs _ s (-1) hinj]
    refine Finset.prod_congr rfl (fun t _ => ?_)
    rw [abs_div]
    congr 2

end GlobalTheory.FamilyDegreeRatio
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem comp_eq_sum_inner_smul_rankOne {H Wp Wq : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {ι κ : Type} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ Wp) (c : OrthonormalBasis κ ℂ Wq)
    (P : H →L[ℂ] Wp) (A : H →L[ℂ] H) (Q : Wq →L[ℂ] H) :
    P.comp (A.comp Q) = ∑ p : ι × κ, ⟪ContinuousLinearMap.adjoint P (b p.1), A (Q (c p.2))⟫_ℂ •
      (innerSL ℂ (c p.2)).smulRight (b p.1) := by
  ext x
  simp only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, Fintype.sum_prod_type, smul_smul]
  conv_lhs => rw [← c.sum_repr' x]

  simp only [map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [← b.sum_repr' (P (A (Q (c j))))]
  simp only [Finset.smul_sum, smul_smul, mul_comm]

theorem isCoef_of_translate_smul_exists : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → (∀ f : Mx k r → (Wq →L[ℂ] Wp), PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f → ∃ s, IsCoef R l l' f s) ∧ (∀ F s (t : ℂ), IsCoef R l l' F s → IsCoef R l l' (fun g => t • F g) (t * s)) ∧ ((∃ x ∈ R.TK, l x ≠ 0) → (∃ y ∈ R.TK, l' y ≠ 0) → ∀ s : ℂ, ∃ F, IsCoef R l l' F s) := by
  intro hK k r ε mu R Wp _ _ _ _ Wq _ _ _ _ l l' hR
  obtain ⟨hmul, hone, hinner, -, -, hTK, hKF, -, -⟩ := rep_basic_of_isDS hK k r ε mu R hR
  refine ⟨?_, ?_, ?_⟩
  · rintro f ⟨a, ha, b, hb, P, Q, hQ, hP, h⟩
    obtain ⟨hai, ha1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv ha
    obtain ⟨hbi, -, hb2⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hb
    let e := stdOrthonormalBasis ℂ Wp
    let c := stdOrthonormalBasis ℂ Wq
    let φ := (finProdFinEquiv (m := Module.finrank ℂ Wp) (n := Module.finrank ℂ Wq)).symm
    refine ⟨_, _, fun i => R.σ a (ContinuousLinearMap.adjoint P (e (φ i).1)),
      fun i => R.σ b⁻¹ (Q (c (φ i).2)), fun i => (innerSL ℂ (c (φ i).2)).smulRight (e (φ i).1),
      fun i => ⟨hTK a ha _ (hKF _ (hP _)), hTK _ hbi _ (hKF _ (hQ _))⟩, fun g hg => ?_, rfl⟩
    have hc : a * (a⁻¹ * g * b⁻¹) * b = g := by
      calc a * (a⁻¹ * g * b⁻¹) * b = (a * a⁻¹) * g * (b⁻¹ * b) := by simp only [Matrix.mul_assoc]
        _ = g := by rw [ha1, hb2, Matrix.one_mul, Matrix.mul_one]
    have h1 : f g = P.comp ((R.σ (a⁻¹ * g * b⁻¹)).comp Q) := by
      have := h (a⁻¹ * g * b⁻¹)
      simpa only [hc] using this
    have hm : a⁻¹ * g * b⁻¹ ∈ GG k r :=
      Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hai hg) hbi
    have h2 : ∀ u v, ⟪u, R.σ (a⁻¹ * g * b⁻¹) v⟫_ℂ = ⟪R.σ a u, R.σ g (R.σ b⁻¹ v)⟫_ℂ := by
      intro u v
      rw [← hinner a ha, ← hmul a ha _ hm, ← hmul g hg _ hbi, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ha1,
        Matrix.one_mul]
    rw [h1, comp_eq_sum_inner_smul_rankOne e c]
    simp only [h2]
    exact (φ.sum_comp (fun p => ⟪R.σ a (ContinuousLinearMap.adjoint P (e p.1)), R.σ g (R.σ b⁻¹ (Q (c p.2)))⟫_ℂ •
      (innerSL ℂ (c p.2)).smulRight (e p.1))).symm
  · rintro F s t ⟨m, x, y, X, hxy, hF, hs⟩
    refine ⟨m, x, y, fun i => t • X i, hxy, fun g hg => ?_, ?_⟩
    · simp only [hF g hg, Finset.smul_sum, smul_smul, mul_comm]
    · simp only [hs, Finset.mul_sum, ContinuousLinearMap.smul_apply, inner_smul_right]
  · rintro ⟨x, hx, hx0⟩ ⟨y, hy, hy0⟩ s
    have h1 : ⟪l x, l x⟫_ℂ ≠ 0 := fun h => hx0 (inner_self_eq_zero.mp h)
    have h2 : ⟪l' y, l' y⟫_ℂ ≠ 0 := fun h => hy0 (inner_self_eq_zero.mp h)
    refine ⟨fun g => ∑ _i : Fin 1, ⟪x, R.σ g y⟫_ℂ •
        ((s / (⟪l' y, l' y⟫_ℂ * ⟪l x, l x⟫_ℂ)) • (innerSL ℂ (l' y)).smulRight (l x)),
      1, fun _ => x, fun _ => y,
      fun _ => (s / (⟪l' y, l' y⟫_ℂ * ⟪l x, l x⟫_ℂ)) • (innerSL ℂ (l' y)).smulRight (l x),
      fun _ => ⟨hx, hy⟩, fun g _ => rfl, ?_⟩
    rw [Fin.sum_univ_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, inner_smul_right, inner_smul_right, div_mul_cancel₀ _ (mul_ne_zero h2 h1)]

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.ComplexifiedAction

open PI.UpqRep GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem gram_herm (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).1

theorem gram_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1

theorem lie_iff {X : Mx k r} : InLieHpk k r X ↔ Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 := Iff.rfl

theorem adj_of_lie {X : Mx k r} (hX : InLieHpk k r X) :
    Formalism.QuantumDeterminants.Hpk k r * Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -X := by
  have h := eq_neg_of_add_eq_zero_left (lie_iff.1 hX)
  rw [Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, gram_sq, Matrix.one_mul]

theorem lie_of_adj {X : Mx k r} (h : Formalism.QuantumDeterminants.Hpk k r * Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -X) : InLieHpk k r X := by
  rw [lie_iff]
  have h2 := congrArg (fun A => Formalism.QuantumDeterminants.Hpk k r * A) h
  simp only [← Matrix.mul_assoc, gram_sq, Matrix.one_mul, Matrix.mul_neg] at h2
  rw [h2, neg_add_cancel]

theorem adj_adj (Y : Mx k r) :
    Formalism.QuantumDeterminants.Hpk k r * (Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r = Y := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, gram_herm, ← Matrix.mul_assoc, gram_sq, Matrix.one_mul]
  rw [Matrix.mul_assoc, gram_sq, Matrix.mul_one]

theorem lie_re (Y : Mx k r) :
    InLieHpk k r ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  apply lie_of_adj
  have e : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, adj_adj, e]
  module

theorem lie_im (Y : Mx k r) :
    InLieHpk k r ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  apply lie_of_adj
  have e : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, adj_adj, e]
  module

theorem exists_decomp (Y : Mx k r) : ∃ X₁ X₂, InLieHpk k r X₁ ∧ InLieHpk k r X₂ ∧ Y = X₁ + Complex.I • X₂ := by
  refine ⟨_, _, lie_re Y, lie_im Y, ?_⟩
  have e : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [smul_smul, e]
  module

theorem adj_decomp {X₁ X₂ : Mx k r} (h₁ : InLieHpk k r X₁) (h₂ : InLieHpk k r X₂) :
    Formalism.QuantumDeterminants.Hpk k r * (X₁ + Complex.I • X₂)ᴴ * Formalism.QuantumDeterminants.Hpk k r = -X₁ + Complex.I • X₂ := by
  have e : star Complex.I = -Complex.I := by simp
  rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    adj_of_lie h₁, adj_of_lie h₂, e]
  module

theorem dC_decomp (R : Rep k r) {X₁ X₂ : Mx k r} (h₁ : InLieHpk k r X₁) (h₂ : InLieHpk k r X₂) (v : R.H) :
    R.dC (X₁ + Complex.I • X₂) v =
      dsig (k := k) (r := r) R.σ X₁ v + Complex.I • dsig (k := k) (r := r) R.σ X₂ v := by
  have e : (1 / (2 * Complex.I)) * (2 * Complex.I) = 1 := by field_simp
  have e1 : (1 / 2 : ℂ) • (X₁ + Complex.I • X₂ + -(-X₁ + Complex.I • X₂)) = X₁ := by module
  have e2 : (1 / (2 * Complex.I)) • (X₁ + Complex.I • X₂ - -(-X₁ + Complex.I • X₂)) = X₂ := by
    have : X₁ + Complex.I • X₂ - -(-X₁ + Complex.I • X₂) = (2 * Complex.I) • X₂ := by module
    rw [this, smul_smul, e, one_smul]
  unfold Rep.dC
  rw [adj_decomp h₁ h₂, e1, e2]

theorem lie_zero : InLieHpk k r 0 := by rw [lie_iff]; simp

theorem lie_add {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) : InLieHpk k r (X + Y) := by
  apply lie_of_adj
  rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul, adj_of_lie hX, adj_of_lie hY, neg_add]

theorem lie_smul (a : ℝ) {X : Mx k r} (hX : InLieHpk k r X) : InLieHpk k r (a • X) := by
  apply lie_of_adj
  rw [conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, adj_of_lie hX, star_trivial, smul_neg]

theorem lie_neg {X : Mx k r} (hX : InLieHpk k r X) : InLieHpk k r (-X) := by
  simpa using lie_smul (-1) hX

theorem lie_br {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) : InLieHpk k r (X * Y - Y * X) := by
  have h1 := eq_neg_of_add_eq_zero_left (lie_iff.1 hX)
  have h2 := eq_neg_of_add_eq_zero_left (lie_iff.1 hY)
  rw [lie_iff]
  generalize Formalism.QuantumDeterminants.Hpk k r = H at h1 h2 ⊢
  have e1 : (X * Y)ᴴ * H = H * (Y * X) := by
    rw [conjTranspose_mul, Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, h2, Matrix.neg_mul, neg_neg,
      Matrix.mul_assoc]
  have e2 : (Y * X)ᴴ * H = H * (X * Y) := by
    rw [conjTranspose_mul, Matrix.mul_assoc, h2, Matrix.mul_neg, ← Matrix.mul_assoc, h1, Matrix.neg_mul, neg_neg,
      Matrix.mul_assoc]
  rw [conjTranspose_sub, Matrix.sub_mul, e1, e2, Matrix.mul_sub]
  abel

theorem dsig_add_left (R : Rep k r) {X Y : Mx k r} (hX : InLieHpk k r X) (hY : InLieHpk k r Y) {v : R.H}
    (hv : v ∈ R.sm) : dsig (k := k) (r := r) R.σ (X + Y) v =
      dsig (k := k) (r := r) R.σ X v + dsig (k := k) (r := r) R.σ Y v := by
  obtain ⟨L, hL⟩ := exists_lin hv
  rw [(hL _ hX).1, (hL _ hY).1, (hL _ (lie_add hX hY)).1, map_add (f := _)]

theorem dsig_smul_left (R : Rep k r) (a : ℝ) {X : Mx k r} (hX : InLieHpk k r X) {v : R.H}
    (hv : v ∈ R.sm) : dsig (k := k) (r := r) R.σ (a • X) v = (a : ℂ) • dsig (k := k) (r := r) R.σ X v := by
  obtain ⟨L, hL⟩ := exists_lin hv
  rw [(hL _ hX).1, (hL _ (lie_smul a hX)).1, map_smul, Complex.coe_smul]

theorem dsig_neg_left (R : Rep k r) {X : Mx k r} (hX : InLieHpk k r X) {v : R.H}
    (hv : v ∈ R.sm) : dsig (k := k) (r := r) R.σ (-X) v = -dsig (k := k) (r := r) R.σ X v := by
  simpa using dsig_smul_left R (-1) hX hv

theorem dC_lie (R : Rep k r) {X : Mx k r} (hX : InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    R.dC X v = dsig (k := k) (r := r) R.σ X v := by
  have h := dC_decomp R hX lie_zero v
  have h0 := dsig_smul_left R 0 hX hv
  rw [zero_smul] at h0
  rw [smul_zero, add_zero, h0] at h
  simpa using h

theorem dC_lin_left (R : Rep k r) (Y Z : Mx k r) (a : ℂ) {v : R.H} (hv : v ∈ R.sm) :
    R.dC (a • Y + Z) v = a • R.dC Y v + R.dC Z v := by
  obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
  obtain ⟨Z₁, Z₂, h3, h4, rfl⟩ := exists_decomp Z
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, a = x + y * Complex.I := ⟨a.re, a.im, (Complex.re_add_im a).symm⟩
  have e : ((x : ℂ) + y * Complex.I) • (Y₁ + Complex.I • Y₂) + (Z₁ + Complex.I • Z₂) =
      (x • Y₁ + (-y) • Y₂ + Z₁) + Complex.I • (y • Y₁ + x • Y₂ + Z₂) := by
    simp only [← Complex.coe_smul]
    push_cast
    linear_combination (norm := module) (y * Complex.I_mul_I) • Y₂
  have a1 := lie_smul x h1
  have a2 := lie_smul (-y) h2
  have a3 := lie_smul y h1
  have a4 := lie_smul x h2
  rw [e, dC_decomp R (lie_add (lie_add a1 a2) h3) (lie_add (lie_add a3 a4) h4), dC_decomp R h1 h2,
    dC_decomp R h3 h4, dsig_add_left R (lie_add a1 a2) h3 hv, dsig_add_left R a1 a2 hv,
    dsig_add_left R (lie_add a3 a4) h4 hv, dsig_add_left R a3 a4 hv, dsig_smul_left R _ h1 hv,
    dsig_smul_left R _ h2 hv, dsig_smul_left R _ h1 hv, dsig_smul_left R _ h2 hv]
  push_cast
  linear_combination (norm := module) (-(y : ℂ) * Complex.I_mul_I) • dsig (k := k) (r := r) R.σ Y₂ v

theorem complexified_action : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → (∀ Y, ∀ v ∈ R.sm, R.dC Y v ∈ R.sm) ∧ (∀ Y (a : ℂ), ∀ v ∈ R.sm, ∀ w ∈ R.sm, R.dC Y (a • v + w) = a • R.dC Y v + R.dC Y w) ∧ (∀ Y Z (a : ℂ), ∀ v ∈ R.sm, R.dC (a • Y + Z) v = a • R.dC Y v + R.dC Z v) ∧ (∀ X, PI.UpqRep.InLieHpk k r X → ∀ v ∈ R.sm, R.dC X v = PI.UpqRep.dsig (k := k) (r := r) R.σ X v) ∧ (∀ Y Z, ∀ v ∈ R.sm, R.dC Y (R.dC Z v) - R.dC Z (R.dC Y v) = R.dC (Y * Z - Z * Y) v) ∧ ∀ Y, ∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪R.dC Y v, w⟫_ℂ = ⟪v, R.dC ((Formalism.QuantumDeterminants.Hpk k r) * Yᴴ * (Formalism.QuantumDeterminants.Hpk k r)) w⟫_ℂ := by
  intro hK k r ε mu R hR
  have hsm : ∀ {X}, InLieHpk k r X → ∀ {v}, v ∈ R.sm → dsig (k := k) (r := r) R.σ X v ∈ R.sm :=
    fun hX _ hv => dsig_smooth hR.2 hX hv
  have hlin : ∀ {X}, InLieHpk k r X → ∀ (a : ℂ) {v w}, v ∈ R.sm → w ∈ R.sm →
      dsig (k := k) (r := r) R.σ X (v + a • w) =
        dsig (k := k) (r := r) R.σ X v + a • dsig (k := k) (r := r) R.σ X w := by
    intro X hX a v w hv hw
    rw [dsig_add hX hv (R.smSub.smul_mem a hw), dsig_smul hX a hw]
  refine ⟨fun Y v hv => ?_, fun Y a v hv w hw => ?_, fun Y Z a v hv => dC_lin_left R Y Z a hv,
    fun X hX v hv => dC_lie R hX hv, fun Y Z v hv => ?_, fun Y v hv w hw => ?_⟩
  · exact R.smSub.add_mem (hsm (lie_re Y) hv) (R.smSub.smul_mem _ (hsm (lie_im Y) hv))
  · obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
    rw [dC_decomp R h1 h2, dC_decomp R h1 h2, dC_decomp R h1 h2, add_comm (a • v) w, hlin h1 a hw hv,
      hlin h2 a hw hv]
    module
  · obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
    obtain ⟨Z₁, Z₂, h3, h4, rfl⟩ := exists_decomp Z
    have e : (Y₁ + Complex.I • Y₂) * (Z₁ + Complex.I • Z₂) - (Z₁ + Complex.I • Z₂) * (Y₁ + Complex.I • Y₂) =
        ((Y₁ * Z₁ - Z₁ * Y₁) + -(Y₂ * Z₂ - Z₂ * Y₂)) + Complex.I • ((Y₁ * Z₂ - Z₂ * Y₁) + (Y₂ * Z₁ - Z₁ * Y₂)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
      linear_combination (norm := module) Complex.I_mul_I • (Y₂ * Z₂ - Z₂ * Y₂)
    have b := GlobalTheory.DerivedBracket.derived_action_bracket hK k r ε mu R hR
    rw [e, dC_decomp R (lie_add (lie_br h1 h3) (lie_neg (lie_br h2 h4))) (lie_add (lie_br h1 h4) (lie_br h2 h3)),
      dsig_add_left R (lie_br h1 h3) (lie_neg (lie_br h2 h4)) hv, dsig_neg_left R (lie_br h2 h4) hv,
      dsig_add_left R (lie_br h1 h4) (lie_br h2 h3) hv, ← b _ _ h1 h3 v hv, ← b _ _ h2 h4 v hv,
      ← b _ _ h1 h4 v hv, ← b _ _ h2 h3 v hv]
    simp only [dC_decomp R h1 h2, dC_decomp R h3 h4]
    rw [hlin h1 _ (hsm h3 hv) (hsm h4 hv), hlin h2 _ (hsm h3 hv) (hsm h4 hv), hlin h3 _ (hsm h1 hv) (hsm h2 hv),
      hlin h4 _ (hsm h1 hv) (hsm h2 hv)]
    linear_combination (norm := module) Complex.I_mul_I • (dsig (k := k) (r := r) R.σ Y₂ (dsig (k := k) (r := r) R.σ Z₂ v) -
      dsig (k := k) (r := r) R.σ Z₂ (dsig (k := k) (r := r) R.σ Y₂ v))
  · obtain ⟨Y₁, Y₂, h1, h2, rfl⟩ := exists_decomp Y
    rw [adj_decomp h1 h2, dC_decomp R h1 h2, dC_decomp R (lie_neg h1) h2, dsig_neg_left R h1 hw, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, inner_neg_right, dsig_skew hR.2 h1 hv hw,
      dsig_skew hR.2 h2 hv hw, Complex.conj_I]
    ring

end GlobalTheory.ComplexifiedAction
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eigenEquation_translation_kernel_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : G ⟶ G) (a : A.A ⟶ A.A), IsMonHom a → (Over.pullback (jK R)).map φ ≫ U.gen.hom = U.gen.hom ≫ a → ∀ (N k : ℕ) (mu : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, φ.left] ![(N : ℤ), -1])), mu.IsGen → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → ∀ (σ₀ : U.SecGF F k) (σ' τ : U.SecGF F (k * N)) (t' t : LB.Sec (LPow A.A A.L ((k * N : ℕ) : ℤ) (TFK (R := R) F))), (∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval σ' (𝟙 _) y J = sval σ₀ (TFK (R := R) F ◁ (Over.pullback (jK R)).map φ).left y J * (val mu (UnifPre.gFK (G := G) F) y J).val ^ k) → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (k * N) (snd (TFK (R := R) F) A.A).left (U.genF F).left t' (UnifPre.gFK (G := G) F) (𝟙 _) σ' → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (k * N) (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) τ → ∀ θ : ThetaGrp A.A A.L ((k * N : ℕ) : ℤ) (TFK (R := R) F), IsActOf A.A A.L ((k * N : ℕ) : ℤ) θ t' t → ∀ (z₀ : TFK (R := R) F ⟶ A.A) (ε : Fˣ), z₀ ≫ a = 1 → WeilIs A.A A.L ((k * N : ℕ) : ℤ) z₀ θ.pt (unitOn ε) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (UnifPre.GF (G := G) F).left) (z : Z) (J), Good U.LG.L z J → sval τ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) (z₀ ≫ U.gen.inv)).left) z J * (val mu (ρ ≫ UnifPre.gFK (G := G) F) z J).val ^ k = constVal (ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) z (ε : F) * (sval τ ρ z J * (val mu ((ρ ≫ (translT ((Over.pullback (jK R)).obj G) (z₀ ≫ U.gen.inv)).left) ≫ UnifPre.gFK (G := G) F) z J).val ^ k) := by
  first | exact @GlobalTheory.Jets.eigen_equation_generic | exact GlobalTheory.Jets.eigen_equation_generic | (intros; apply GlobalTheory.Jets.eigen_equation_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

noncomputable section

namespace GlobalTheory.DepthLink

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring

end GlobalTheory.DepthLink
end
end
