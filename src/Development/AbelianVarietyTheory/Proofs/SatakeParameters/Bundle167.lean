module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformTrivialPhaseSkewHermitian
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle028
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle024
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelVectorGoodTypeStableSubspace
import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Formalism.LocalToGlobal.HermitianForms.Bundle002
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
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle017
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsLat
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.AlgebraMapFinite
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle001
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.Bundle008
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

section

open Matrix

noncomputable section

namespace GlobalTheory.Hk3.CayleyCong

open GlobalTheory.Hk3.CayleyPhase GlobalTheory.Hk3.IntWitt

theorem cayley_cong : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) → (∀ r s, C r s ∈ Formalism.UG.intL L) →
    ∀ k : ℕ, 1 ≤ k →
    ∃ g : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (g : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      (∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s)) ∧
      ∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s -
        (ϖ ^ k • (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * C)) r s) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT hermT C hskew hCI k hk
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  have hσv := hU.2.1
  have hσϖ : σ ϖ = ϖ := hU.2.2.1
  have hvϖ : Valued.v ϖ < 1 := by
    rw [hU.2.2.2.1]; exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) < 1 by decide)
  have hϖI : ϖ ∈ Formalism.UG.intL L := le_of_lt hvϖ
  have hvϖk : Valued.v (ϖ ^ k) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ zero_le' hvϖ (by omega)
  have hhalf : Valued.v ((2 : L)⁻¹) ≤ 1 := by rw [map_inv₀, h2, inv_one]
  have hσhalf : σ ((2 : L)⁻¹) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  set Jt : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJt
  set Jti : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJti
  have hJtiI : IsIntM Jti := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint (inv_mem hJT)
  have hJJi : Jt * Jti = 1 := by rw [hJt, hJti, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcJt : Formalism.UG.cT σ Jt = Jt := cT_herm σ hermT
  have hcC : Formalism.UG.cT σ C = -C := cT_skew σ hskew
  have hcJti : Formalism.UG.cT σ Jti * Jt = 1 := by
    calc Formalism.UG.cT σ Jti * Jt = Formalism.UG.cT σ Jti * Formalism.UG.cT σ Jt := by rw [hcJt]
      _ = Formalism.UG.cT σ (Jt * Jti) := (Formalism.UG.cT_mul σ _ _).symm
      _ = 1 := by rw [hJJi, Formalism.UG.cT_one]
  set M : Matrix (Fin n') (Fin n') L := Jti * C with hMdef
  have hMI : IsIntM M := isIntM_mul hJtiI hCI
  set Y : Matrix (Fin n') (Fin n') L := ϖ ^ k • M with hYdef
  have hσϖk : σ (ϖ ^ k) = ϖ ^ k := by rw [map_pow, hσϖ]
  have hY : Formalism.UG.cT σ Y * Jt = -(ϖ ^ k • C) := by
    rw [hYdef, cT_smul, hσϖk, Matrix.smul_mul, hMdef, Formalism.UG.cT_mul, hcC, Matrix.mul_assoc, hcJti, Matrix.mul_one,
      smul_neg]
  have hJY : Jt * Y = ϖ ^ k • C := by
    rw [hYdef, Matrix.mul_smul, hMdef, ← Matrix.mul_assoc, hJJi, Matrix.one_mul]
  set Z : Matrix (Fin n') (Fin n') L := (2⁻¹ : L) • Y with hZdef
  have hZZ : Z + Z = Y := by
    rw [hZdef, ← add_smul]
    have : (2⁻¹ + 2⁻¹ : L) = 1 := by
      have h2ne : (2 : L) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
      field_simp; norm_num
    rw [this, one_smul]
  have hZ : Formalism.UG.cT σ Z * Jt = -(Jt * Z) := by
    rw [hZdef, cT_smul, hσhalf, Matrix.smul_mul, hY, Matrix.mul_smul, hJY, smul_neg]
  have hYsmall : IsSmallM Y := fun i j => by
    rw [hYdef, Matrix.smul_apply, smul_eq_mul]; exact lt_one_mul hvϖk (hMI i j)
  have hZsmall : IsSmallM Z := small_smul hhalf hYsmall
  obtain ⟨hPdet, hPiI⟩ := inv_one_sub hZsmall
  obtain ⟨hQdet, hQiI⟩ := inv_one_add hZsmall
  set Pi := (1 - Z)⁻¹ with hPi
  set Qi := (1 + Z)⁻¹ with hQi
  have hP1 : Pi * (1 - Z) = 1 := Matrix.nonsing_inv_mul _ hPdet
  have hP2 : (1 - Z) * Pi = 1 := Matrix.mul_nonsing_inv _ hPdet
  have hQ1 : Qi * (1 + Z) = 1 := Matrix.nonsing_inv_mul _ hQdet
  have hQ2 : (1 + Z) * Qi = 1 := Matrix.mul_nonsing_inv _ hQdet
  have hPs : Formalism.UG.cT σ Pi * (1 - Formalism.UG.cT σ Z) = 1 := by
    rw [← Formalism.UG.cT_one σ, ← cT_sub, ← Formalism.UG.cT_mul, hP2]
  let g : GL (Fin n') L := ⟨Pi * (1 + Z), Qi * (1 - Z), by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + Z), hQ2, Matrix.one_mul, hP1], by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - Z), hP2, Matrix.one_mul, hQ1]⟩
  have hgU : g ∈ Formalism.UG.UJ σ Jt := by
    show Formalism.UG.cT σ (Pi * (1 + Z)) * Jt * (Pi * (1 + Z)) = Jt
    rw [Formalism.UG.cT_mul, cT_add, Formalism.UG.cT_one]
    exact cayley_unitary_ring hZ hP1 hP2 hQ1 hQ2 hPs
  have hone : IsIntM (1 : Matrix (Fin n') (Fin n') L) := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hIZ : IsIntM (1 + Z) := isIntM_add hone (isIntM_of_small hZsmall)
  have hIZ' : IsIntM (1 - Z) := by
    rw [sub_eq_add_neg]; exact isIntM_add hone (isIntM_neg (isIntM_of_small hZsmall))
  have hgI : g ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) :=
    mem_GLint_of_int (isIntM_mul hPiI hIZ) (isIntM_mul hQiI hIZ')
  obtain ⟨hr1, hr2⟩ := cayley_ring hP1 hP2
  have hg1 : Pi * (1 + Z) - 1 = ϖ ^ k • (M * Pi) := by
    rw [hr1, hZZ, hYdef, Matrix.smul_mul]
  have hg2 : Pi * (1 + Z) - 1 - Y = (ϖ ^ (k + 1) * (ϖ ^ (k - 1) * 2⁻¹)) • (M * Pi * M) := by
    have e : ϖ ^ (k + 1) * (ϖ ^ (k - 1) * 2⁻¹) = ϖ ^ k * (2⁻¹ * ϖ ^ k) := by
      have : k + 1 + (k - 1) = k + k := by omega
      rw [← mul_assoc, ← pow_add, this, pow_add]; ring
    rw [e, hr1, hZZ]
    have e2 : Y * Pi - Y = Y * (Pi - 1) := by rw [Matrix.mul_sub, Matrix.mul_one]
    rw [e2, hr2, hZdef, hYdef]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc]
    congr 1; ring
  refine ⟨⟨g, hgU⟩, hgI, fun r s => ?_, fun r s => ?_⟩
  · have : ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) r s - (1 : Matrix (Fin n') (Fin n') L) r s =
        (Pi * (1 + Z) - 1) r s := by rw [Matrix.sub_apply]
    rw [this, hg1, Matrix.smul_apply, smul_eq_mul]
    exact ⟨_, isIntM_mul hMI hPiI r s, rfl⟩
  · have : ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) r s - (1 : Matrix (Fin n') (Fin n') L) r s -
        (ϖ ^ k • (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * C)) r s =
        (Pi * (1 + Z) - 1 - Y) r s := by rw [Matrix.sub_apply, Matrix.sub_apply]
    rw [this, hg2, Matrix.smul_apply, smul_eq_mul, mul_assoc]
    refine ⟨_, mul_mem (mul_mem (pow_mem hϖI _) hhalf) (isIntM_mul (isIntM_mul hMI hPiI) hMI r s), rfl⟩

end GlobalTheory.Hk3.CayleyCong
end
end

section

open Matrix

noncomputable section

namespace GlobalTheory.Hk3.SkewLift

open GlobalTheory.Hk3.CayleyPhase GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L]

theorem cT_cT (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) {a b : Type} (M : Matrix a b L) :
    Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
  ext i j; simp [Formalism.UG.cT, hσ]

theorem cT_mul_rect (σ : L →+* L) {a b c : Type} [Fintype b] (M : Matrix a b L) (N : Matrix b c L) :
    Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
  ext i j; simp [Formalism.UG.cT, Matrix.mul_apply, map_sum, mul_comm]

theorem isIntM_sub' [Valued L (WithZero (Multiplicative ℤ))] {a b : Type} {M N : Matrix a b L} (hM : IsIntM M) (hN : IsIntM N) : IsIntM (M - N) :=
  fun i j => sub_mem (hM i j) (hN i j)

theorem skew_lift : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (z w a : ι → Fin n' → L),
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, w i r ∈ Formalism.UG.intL L) → (∀ i r, a i r ∈ Formalism.UG.intL L) →
    (∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (w j) +
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (w i) (z j))) →
    ∃ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) ∧ (∀ r s, C r s ∈ Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((C *ᵥ z i) r - ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w i) r) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT herm ι _ _ z w a hz hw ha hdual hcong
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  have hσσ := hU.1
  have hσv := hU.2.1
  have hhalf : (2 : L)⁻¹ ∈ Formalism.UG.intL L := by
    show Valued.v ((2 : L)⁻¹) ≤ 1
    rw [map_inv₀, h2, inv_one]
  have hσhalf : σ ((2 : L)⁻¹) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hJI : IsIntM J := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint hJT
  have hcJ : Formalism.UG.cT σ J = J := cT_herm σ herm
  let B : Matrix (Fin n') ι L := fun r i => (J *ᵥ w i) r
  let Z : Matrix (Fin n') ι L := fun r j => z j r
  let A : Matrix ι (Fin n') L := fun i r => a i r
  let P : Matrix ι ι L := Formalism.UG.cT σ B * Z
  let C : Matrix (Fin n') (Fin n') L :=
    B * A - Formalism.UG.cT σ A * Formalism.UG.cT σ B + (2⁻¹ : L) • (Formalism.UG.cT σ A * (P - Formalism.UG.cT σ P) * A)
  have hAZ : A * Z = 1 := by
    ext i j; rw [Matrix.mul_apply, Matrix.one_apply]; exact hdual i j
  have hAI : IsIntM A := fun i r => ha i r
  have hZI : IsIntM Z := fun r j => hz j r
  have hBI : IsIntM B := fun r i => by
    show (J *ᵥ w i) r ∈ Formalism.UG.intL L
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun s _ => mul_mem (hJI r s) (hw i s)
  have hPI : IsIntM P := isIntM_mul (isIntM_cT hσv hBI) hZI
  have hcC : Formalism.UG.cT σ C = -C := by
    simp only [C, cT_add, cT_sub, cT_smul, cT_mul_rect, cT_cT σ hσσ, hσhalf]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, smul_sub, neg_add, neg_sub]
  refine ⟨C, ?_, ?_, ?_⟩
  · intro r s
    have := congrFun (congrFun hcC s) r
    simpa [Formalism.UG.cT] using this
  · exact isIntM_add (isIntM_sub' (isIntM_mul hBI hAI) ((isIntM_mul (isIntM_cT hσv hAI) (isIntM_cT hσv hBI))))
      (isIntM_smul hhalf (isIntM_mul (isIntM_mul (isIntM_cT hσv hAI) (isIntM_sub' hPI (isIntM_cT hσv hPI))) hAI))
  · have hP : ∀ k i, P k i = Formalism.UG.hform σ J (w k) (z i) := by
      intro k i
      show ∑ r, σ (B r k) * z i r = _

      simp only [B, Formalism.UG.hform, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.mulVec, dotProduct, map_sum, map_mul, herm, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    have hσh : ∀ x y : Fin n' → L, σ (Formalism.UG.hform σ J x y) = Formalism.UG.hform σ J y x := by
      intro x y

      simp only [Formalism.UG.hform, map_sum, map_mul, hσσ, herm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    have hS : ∀ k i, DvdPow ϖ 1 ((P + Formalism.UG.cT σ P) k i) := by
      intro k i
      have e : (P + Formalism.UG.cT σ P) k i = Formalism.UG.hform σ J (z k) (w i) + Formalism.UG.hform σ J (w k) (z i) := by
        show P k i + σ (P i k) = _
        rw [hP, hP, hσh, add_comm]
      rw [e]; exact hcong k i
    have hCZ : C * Z = B - (2⁻¹ : L) • (Formalism.UG.cT σ A * (P + Formalism.UG.cT σ P)) := by
      have e1 : C * Z = B * (A * Z) - Formalism.UG.cT σ A * P + (2⁻¹ : L) • (Formalism.UG.cT σ A * (P - Formalism.UG.cT σ P) * (A * Z)) := by
        simp only [C, P, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]
      rw [e1, hAZ, Matrix.mul_one, Matrix.mul_one]
      have e2 : Formalism.UG.cT σ A * P = (2⁻¹ : L) • (Formalism.UG.cT σ A * P) + (2⁻¹ : L) • (Formalism.UG.cT σ A * P) := by
        rw [← add_smul]
        have : (2⁻¹ + 2⁻¹ : L) = 1 := by
          have h2ne : (2 : L) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
          field_simp; norm_num
        rw [this, one_smul]
      rw [e2, Matrix.mul_add, Matrix.mul_sub, smul_add, smul_sub]
      abel
    intro i r
    have e : (C *ᵥ z i) r - (J *ᵥ w i) r = (C * Z) r i - B r i := rfl
    rw [e, hCZ, Matrix.sub_apply, sub_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
    refine dvdPow_neg (dvdPow_sum _ _ fun k _ => ?_)
    rw [← mul_assoc]
    exact dvdPow_mul_int (hS k i) (mul_mem hhalf (isIntM_cT hσv hAI r k))

end GlobalTheory.Hk3.SkewLift
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory.TwV.Xc

theorem not_dvd_absDifferent_of_not_mem_sq {E : Type} [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (P : HeightOneSpectrum (𝓞 E)) (h1 : ((p : ℕ) : 𝓞 E) ∈ P.asIdeal)
    (h2 : ((p : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) : ¬ P.asIdeal ∣ differentIdeal ℤ (𝓞 E) := by
  have hP : P.asIdeal.IsMaximal := P.isMaximal
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime _
  have : Finite (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod p).toEquiv.symm
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((p : ℕ) : ℤ)}) =
      Ideal.span {((p : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((p : ℕ) : ℤ)}) ≤ P.asIdeal := by
    rw [hmap, Ideal.span_singleton_le_iff_mem]
    exact h1
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 hle
  have hcop : IsCoprime P.asIdeal Q := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have heq := hP.eq_of_le hne le_sup_left
    have hQP : Q ≤ P.asIdeal := heq ▸ le_sup_right
    apply h2
    have hmem : ((p : ℕ) : 𝓞 E) ∈
        Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((p : ℕ) : ℤ)}) := by
      rw [hmap]; exact Ideal.subset_span rfl
    rw [hQ] at hmem
    rw [pow_two]
    exact Ideal.mul_mono_right hQP hmem
  exact not_dvd_differentIdeal_of_isCoprime ℤ P.asIdeal Q hcop hQ.symm

theorem inverseHalfDifferent_local_trivial_at_prime_norm : ∀ (D : D7) (p : ℕ), p.Prime → ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ((p : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  intro D p hp P h1 h2
  have hnd := not_dvd_absDifferent_of_not_mem_sq p hp P h1 h2
  have ht : differentIdeal ℤ (𝓞 D.host.E) = differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) *
      (differentIdeal ℤ (𝓞 D.host.K)).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) :=
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E)
  have hspec : D.host.𝔟 ∣ differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) := ⟨_, D.host.𝔟_spec.1⟩
  have hn : ¬ D.host.𝔟 ≤ P.asIdeal := fun h => hnd (by
    rw [ht]
    exact ((Ideal.dvd_iff_le.2 h).trans hspec).mul_right _)
  obtain ⟨t, htb, htP⟩ := SetLike.not_le_iff_exists.1 hn
  have hb : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => hn (h ▸ bot_le)
  ext x
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨t * s, fun h => (P.isPrime.mem_or_mem h).elim htP hs, ?_⟩
    obtain ⟨u, hu⟩ := (FractionalIdeal.mem_one_iff _).1
      ((FractionalIdeal.mem_inv_iff hb).1 hx _ (FractionalIdeal.mem_coeIdeal_of_mem _ htb))
    rw [Submodule.mem_one]
    refine ⟨u, ?_⟩
    rw [hu, mul_smul, Algebra.smul_def t, mul_comm]
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    obtain ⟨u, hu⟩ := Submodule.mem_one.1 hx
    refine (FractionalIdeal.mem_inv_iff hb).2 fun y hy => ?_
    obtain ⟨z, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_one_iff _).2 ⟨u * z, by rw [map_mul, hu]⟩

end GlobalTheory.TwV.Xc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_level_vector_goodType_stable_subspace : ∀ {K G W : Type} [Field K] [CharZero K] [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : K →+* ℂ) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) (ρ : Representation ℂ G W) (U : Submodule ℂ W), (∀ χ ∈ X, IsAbsIrrChar χ) → (∀ χ ∈ X, chiIdem χ * lvlIdem P ψ ≠ 0) → (∀ g, U.map (ρ g) ≤ U) → U ≠ ⊥ → (∀ u ∈ U, ∑ g, σ ((idemOf X).coeff g) • ρ g u = u) → ∃ u ∈ U, u ≠ 0 ∧ ∀ p : P, ρ p u = σ (ψ p : K) • u := by
  first | exact @GlobalTheory.Hk3.exists_level_vector | exact GlobalTheory.Hk3.exists_level_vector | (intros; apply GlobalTheory.Hk3.exists_level_vector <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct



namespace GlobalTheory.DivInt
open GlobalTheory.AdeleBaseChange Formalism.UG.P

theorem exists_nat_mul_div_pow_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (w : HeightOneSpectrum (𝓞 F)) (z : AfE F E), (∀ w', w' ≠ w → prV (E := E) w' z = 0) → ∀ (ℓ : ℕ), ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal → ∃ D : ℕ, 0 < D ∧ ∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E := by
  intro F E _ _ _ _ _ w z hz ℓ hℓ
  obtain ⟨ι, hι⟩ := exists_toAd F E
  obtain ⟨x, r, hr, hzr⟩ := exists_approx z
  obtain ⟨D, hD, hDx⟩ := exists_nat_mul_integral ({x} : Finset E)
  obtain ⟨o, ho⟩ := hDx x (Finset.mem_singleton_self x)
  have hDz : algebraMap E _ (D : E) * ι z ∈ intAd E := by
    rw [hzr, map_add (f := _), map_tmul_one hι, mul_add, ← map_mul, ← nsmul_eq_mul, ← ho]
    exact add_mem (algebraMap_int_mem o) (mul_mem (by
      rw [← map_natCast (algebraMap (𝓞 E) E)]; exact algebraMap_int_mem _) (map_mem_int hι hr))
  refine ⟨D, hD, fun n => mem_int_of_map hι ?_⟩
  intro P
  rw [map_mul, map_tmul_one hι]
  change algebraMap E (P.adicCompletion E) ((D : E) / (ℓ : E) ^ n) * ι z P ∈ P.adicCompletionIntegers E
  by_cases hP : P.under (𝓞 F) = w
  · have hv : Valued.v (algebraMap E (P.adicCompletion E) (ℓ : E)) = 1 := by
      rw [levelaf_valued_algebraMap, ← map_natCast (algebraMap (𝓞 E) E),
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      intro hm
      apply hℓ
      rw [← hP, HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]
      exact hm
    have h1 := hDz P
    change algebraMap E (P.adicCompletion E) (D : E) * ι z P ∈ P.adicCompletionIntegers E at h1
    have e : algebraMap E (P.adicCompletion E) ((D : E) / (ℓ : E) ^ n) * ι z P =
        (algebraMap E (P.adicCompletion E) (ℓ : E))⁻¹ ^ n *
          (algebraMap E (P.adicCompletion E) (D : E) * ι z P) := by
      rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, inv_pow]; ring
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 ⊢
    rw [e, map_mul, map_pow, map_inv₀, hv, inv_one, one_pow, one_mul]
    exact h1
  · have h0 : ι z P = 0 := (prV_eq_zero_iff hι (P.under (𝓞 F)) z).1 (hz _ hP) P rfl
    rw [h0, mul_zero]
    exact zero_mem _

end GlobalTheory.DivInt
end

section

noncomputable section
namespace GlobalTheory.TwU
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section OneByOne
variable {R : Type} [CommRing R]

end OneByOne

variable {D : D7}

theorem det_mem_normOne_of_mem_unitaryPoints {n : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} (hJ : IsUnit J.det)
    {g : GL (Fin n) (AfE D.host.F D.host.E)} (hg : g ∈ UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    Matrix.GeneralLinearGroup.det g ∈ U1 (sigD D) := by
  set σR := Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  have h0 : Formalism.UG.cT σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)) * J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) *
      (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)) = J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := hg
  have h1 := congrArg Matrix.det h0
  simp only [Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose] at h1
  have e1 : ((g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).map σR).det = σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det := by
    rw [RingHom.map_det]; rfl
  have e2 : (J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))).det = Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det := by
    rw [RingHom.map_det]; rfl
  rw [e1, e2] at h1
  have hu : IsUnit (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det) := hJ.map _
  have h2 : σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det * (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det = 1 := by
    have : (σR (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det * (g : Matrix (Fin n) (Fin n) (AfE D.host.F D.host.E)).det) *
        Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det = 1 * Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) J.det := by
      linear_combination h1
    exact hu.mul_right_cancel this
  show _ = _
  apply Units.ext
  simp only [MonoidHom.mul_apply, MonoidHom.id_apply, Units.val_mul, conjId, Units.coe_map, Units.val_one,
    Matrix.GeneralLinearGroup.val_det_apply]
  rw [mul_comm]
  exact h2

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup}


end GlobalTheory.TwU
end
end
