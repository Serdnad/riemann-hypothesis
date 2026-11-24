module

import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasDerivAtExpMul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KStableFiniteDimSmoothCompactRootStable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusWeightEigenAndRootShift
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
public import Formalism.RealPlaceAnalysis.StatementKT
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyExistsAndAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DominantRootSums
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Lemma

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.KStableFiniteDimSmoothCompactRootStable, CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TorusWeightEigenAndRootShift, CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsLowestKFiniteVectorDiscreteSeries, CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsLowestKFiniteVectorDiscreteSeriesStatement

-- ===== clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.KStableFiniteDimSmoothCompactRootStable =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.KStableFiniteDimSmoothCompactRootStable", "h": "module\n\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG\npublic import Mathlib.Analysis.LocallyConvex.AbsConvexOpen\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompactStable

open PI.UpqRep

theorem deriv_mem {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    {f : ℝ → H} {f' : H} (hf : HasDerivAt f f' 0) (hS : ∀ t, f t ∈ S) : f' ∈ S := by
  have h := hasDerivAt_iff_tendsto_slope.1 hf
  refine S.closed_of_finiteDimensional.mem_of_tendsto h (Filter.Eventually.of_forall fun t => ?_)
  rw [slope_def_module]
  exact S.smul_of_tower_mem _ (S.sub_mem (hS t) (hS 0))

variable {k r : ℕ}

theorem dsig_mem (R : Rep k r) (S : Submodule ℂ R.H) [FiniteDimensional ℂ S]
    (hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S)
    {X : Mx k r} (hX : Xᴴ = -X) (hc : Hpk k r * X = X * Hpk k r) {v : R.H} (hv : v ∈ S) (hsm : v ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X v ∈ S := by
  have hL : InLieHpk k r X := by
    show Xᴴ * Hpk k r + Hpk k r * X = 0
    rw [hX, hc]; simp
  refine deriv_mem S (GlobalTheory.DerivedAction.hasDerivAt_dsig hL hsm) fun t => hS _ ⟨GlobalTheory.DerivedAction.exp_mem hL t, ?_⟩ v hv
  have h := CCRuleCW.exp_mem_UH 1 ((t : ℂ) • X) (by
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hX]; simp)
  have h' : (NormedSpace.exp ((t : ℂ) • X))ᴴ * 1 * NormedSpace.exp ((t : ℂ) • X) = 1 := h
  rw [Matrix.mul_one] at h'
  exact Matrix.mem_unitaryGroup_iff'.2 h'

theorem dC_mem (R : Rep k r) (S : Submodule ℂ R.H) [FiniteDimensional ℂ S]
    (hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S)
    (h1 : (Hpk k r)ᴴ = Hpk k r) (h2 : Hpk k r * Hpk k r = 1)
    {Y : Mx k r} (hc : Hpk k r * Y = Y * Hpk k r) {v : R.H} (hv : v ∈ S) (hsm : v ∈ R.sm) :
    R.dC Y v ∈ S :=
  _root_.GlobalTheory.CompactStable.dC_mem R S hS h1 h2 hc hv hsm

theorem Jm_single {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    Jm ε * Matrix.single a b (1 : ℂ) = Matrix.single a b 1 * Jm ε := by
  ext i j
  unfold Jm
  rw [diagonal_mul, mul_diagonal]
  by_cases hij : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := hij
    simp [h]
  · simp [Matrix.single, hij]

theorem kStable_smooth_and_stable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → ∀ S : Submodule ℂ R.H, FiniteDimensional ℂ S → PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S → (∀ v ∈ S, R.KFin v ∧ v ∈ R.sm) ∧ ∀ a b, ε a = ε b → ∀ v ∈ S, R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v ∈ S := by
  intro hK k r ε mu R hR Q hQ S hfd hst
  have hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S := by
    intro g hg x hx
    obtain ⟨hk, hback⟩ := PI.UnitaryGroupMassFormula.LowSmooth.conj_mem_Kset hQ hg
    have h := hst _ hk x hx
    simp only [hback] at h
    exact h
  have hA : ∀ v ∈ S, R.KFin v ∧ v ∈ R.sm := fun v hv =>
    ⟨⟨S, hfd, hv, hS⟩, hK k r ε mu R.H R.σ hR.1 hR.2 v ⟨S, hfd, hv, hS⟩⟩
  refine ⟨hA, fun a b hab v hv => ?_⟩
  have hsP : Qᴴ * Q = 1 := Matrix.mem_unitaryGroup_iff'.mp hQ.2
  have hPs : Q * Qᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hQ.2
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv hsP
  have hH : Qᴴ * Jm ε * Q = Hpk k r := hQ.1.2
  have hJ1 : (Jm ε)ᴴ = Jm ε := by
    unfold Jm
    rw [diagonal_conjTranspose]
    congr 1
    funext c
    by_cases hc : ε c = true <;> simp [hc]
  have hJ2 : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext c
    by_cases hc : ε c = true <;> simp [hc]
  have hm : ∀ A B : Mx k r, Qᴴ * A * Q * (Qᴴ * B * Q) = Qᴴ * (A * B) * Q := by
    intro A B
    calc Qᴴ * A * Q * (Qᴴ * B * Q) = Qᴴ * A * (Q * Qᴴ) * B * Q := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * (A * B) * Q := by rw [hPs, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  refine dC_mem R S hS ?_ ?_ ?_ hv (hA v hv).2
  · rw [← hH, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ1, Matrix.mul_assoc]
  · rw [← hH, hm, hJ2, Matrix.mul_one, hsP]
  · rw [← hH, hinv, hm, hm, Jm_single ε hab]

end GlobalTheory.CompactStable
end Gp91 -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.KStableFiniteDimSmoothCompactRootStable =====

-- ===== clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TorusWeightEigenAndRootShift =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TorusWeightEigenAndRootShift", "h": "module\n\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.Normed.Algebra.MatrixExponential\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TorusWeight

open PI.UpqRep _root_.Gp91.GlobalTheory.DerivedAction

section alg

variable {n : Type} [Fintype n] [DecidableEq n] {G : Matrix n n ℂ}

theorem part_one_lie (h1 : Gᴴ = G) (h2 : G * G = 1) (Y : Matrix n n ℂ) :
    ((1 / 2 : ℂ) • (Y + -(G * Yᴴ * G)))ᴴ * G + G * ((1 / 2 : ℂ) • (Y + -(G * Yᴴ * G))) = 0 := by
  have e1 : (G * Yᴴ * G)ᴴ * G = G * Y := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, h1, Matrix.mul_assoc, h2, Matrix.mul_one]
  have e2 : G * (G * Yᴴ * G) = Yᴴ * G := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have e3 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [conjTranspose_smul, e3, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, conjTranspose_add,
    conjTranspose_neg, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, e1, e2]
  simp

theorem part_two_lie (h1 : Gᴴ = G) (h2 : G * G = 1) (Y : Matrix n n ℂ) :
    ((1 / (2 * Complex.I)) • (Y - -(G * Yᴴ * G)))ᴴ * G +
      G * ((1 / (2 * Complex.I)) • (Y - -(G * Yᴴ * G))) = 0 := by
  have e1 : (G * Yᴴ * G)ᴴ * G = G * Y := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, h1, Matrix.mul_assoc, h2, Matrix.mul_one]
  have e2 : G * (G * Yᴴ * G) = Yᴴ * G := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have e3 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp
  rw [conjTranspose_smul, e3, Matrix.smul_mul, Matrix.mul_smul, neg_smul, ← smul_neg, ← smul_add,
    conjTranspose_sub,
    conjTranspose_neg, Matrix.sub_mul, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_neg, e1, e2]
  have : -(Yᴴ * G - -(G * Y)) + (G * Y - -(Yᴴ * G)) = 0 := by abel
  rw [this, smul_zero]

theorem theta_conj (h2 : G * G = 1) {g : Matrix n n ℂ} (hu : IsUnit g.det) (hU : gᴴ * G * g = G)
    (Y : Matrix n n ℂ) : g * (G * Yᴴ * G) * g⁻¹ = G * (g * Y * g⁻¹)ᴴ * G := by
  have hi1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have A : (g⁻¹)ᴴ * G = G * g := by
    calc (g⁻¹)ᴴ * G = (g⁻¹)ᴴ * (gᴴ * G * g) := by rw [hU]
      _ = (g * g⁻¹)ᴴ * G * g := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = G * g := by rw [hi1, conjTranspose_one, Matrix.one_mul]
  have A' : G * (g⁻¹)ᴴ = g * G := by
    calc G * (g⁻¹)ᴴ = G * ((g⁻¹)ᴴ * G) * G := by
          simp only [Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = (G * G) * g * G := by rw [A]; simp only [Matrix.mul_assoc]
      _ = g * G := by rw [h2, Matrix.one_mul]
  have B : G * g⁻¹ = gᴴ * G := by
    calc G * g⁻¹ = gᴴ * G * g * g⁻¹ := by rw [hU]
      _ = gᴴ * G := by rw [Matrix.mul_assoc, hi1, Matrix.mul_one]
  calc g * (G * Yᴴ * G) * g⁻¹ = (g * G) * Yᴴ * (G * g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = (G * (g⁻¹)ᴴ) * Yᴴ * (gᴴ * G) := by rw [A', B]
    _ = _ := by simp only [conjTranspose_mul, Matrix.mul_assoc]

omit [DecidableEq n] in
theorem part_one_smul (x y : ℝ) (Y : Matrix n n ℂ) :
    (1 / 2 : ℂ) • (((x : ℂ) + y * Complex.I) • Y + -(G * (((x : ℂ) + y * Complex.I) • Y)ᴴ * G)) =
      x • ((1 / 2 : ℂ) • (Y + -(G * Yᴴ * G))) - y • ((1 / (2 * Complex.I)) • (Y - -(G * Yᴴ * G))) := by
  rw [conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  generalize G * Yᴴ * G = Z
  have e : (1 / (2 * Complex.I)) = -Complex.I / 2 := by
    field_simp; simp
  rw [e]
  ext i j
  simp
  ring

omit [DecidableEq n] in
theorem part_two_smul (x y : ℝ) (Y : Matrix n n ℂ) :
    (1 / (2 * Complex.I)) • (((x : ℂ) + y * Complex.I) • Y - -(G * (((x : ℂ) + y * Complex.I) • Y)ᴴ * G)) =
      x • ((1 / (2 * Complex.I)) • (Y - -(G * Yᴴ * G))) + y • ((1 / 2 : ℂ) • (Y + -(G * Yᴴ * G))) := by
  rw [conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  generalize G * Yᴴ * G = Z
  have e : (1 / (2 * Complex.I)) = -Complex.I / 2 := by
    field_simp; simp
  rw [e]
  ext i j
  simp
  linear_combination (-(y : ℂ) / 2 * Y i j + (y : ℂ) / 2 * Z i j) * Complex.I_mul_I

end alg

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}

theorem dC_smul_left (h1 : (Hpk k r)ᴴ = Hpk k r) (h2 : Hpk k r * Hpk k r = 1) (R : Rep k r) (c : ℂ)
    (Y : Mx k r) {v : R.H} (hv : v ∈ R.sm) : R.dC (c • Y) v = c • R.dC Y v := by
  obtain ⟨L, hL⟩ := exists_lin hv
  have hE : Formalism.QuantumDeterminants.Hpk k r = Hpk k r := rfl
  unfold Rep.dC
  rw [hE, (hL _ (part_one_lie h1 h2 _)).1, (hL _ (part_one_lie h1 h2 _)).1,
    (hL _ (part_two_lie h1 h2 _)).1, (hL _ (part_two_lie h1 h2 _)).1]
  rw [← Complex.re_add_im c, part_one_smul, part_two_smul]
  generalize (1 / 2 : ℂ) • (Y + -(Hpk k r * Yᴴ * Hpk k r)) = X₁
  generalize (1 / (2 * Complex.I)) • (Y - -(Hpk k r * Yᴴ * Hpk k r)) = X₂
  rw [map_sub, map_add (f := _), map_smul, map_smul, map_smul, map_smul]
  generalize L X₁ = A
  generalize L X₂ = B
  simp only [← Complex.coe_smul]
  match_scalars
  · ring
  · linear_combination (-(c.im : ℂ)) * Complex.I_mul_I

theorem dC_smul_right (h1 : (Hpk k r)ᴴ = Hpk k r) (h2 : Hpk k r * Hpk k r = 1) (R : Rep k r) (c : ℂ)
    (Y : Mx k r) {v : R.H} (hv : v ∈ R.sm) : R.dC Y (c • v) = c • R.dC Y v := by
  have hE : Formalism.QuantumDeterminants.Hpk k r = Hpk k r := rfl
  unfold Rep.dC
  rw [hE, dsig_smul (part_one_lie h1 h2 _) c hv, dsig_smul (part_two_lie h1 h2 _) c hv,
    smul_comm Complex.I c, ← smul_add]

theorem dC_conj (hK : PI.KFinSmooth) (R : Rep k r) (hR : R.IsDG ε mu)
    (h1 : (Hpk k r)ᴴ = Hpk k r) (h2 : Hpk k r * Hpk k r = 1) {g : Mx k r} (hg : g ∈ GG k r)
    (hu : IsUnit g.det) (Y : Mx k r) {v : R.H} (hv : v ∈ R.sm) :
    R.σ g (R.dC Y v) = R.dC (g * Y * g⁻¹) (R.σ g v) := by
  have hE : Formalism.QuantumDeterminants.Hpk k r = Hpk k r := rfl
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold Rep.dC
  rw [hE, map_add (f := _), map_smul,
    (derived_action hK k r ε mu R hR _ (part_one_lie h1 h2 Y)).2.1 v hv g hg,
    (derived_action hK k r ε mu R hR _ (part_two_lie h1 h2 Y)).2.1 v hv g hg,
    ← theta_conj h2 hu hU]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul]

theorem torus_mem_K {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε := by
  apply _root_.GlobalTheory.CompanionTheory.WtLinkPf.tor_mem_K <;> assumption

theorem torus_single {n : ℕ} (θ : Fin n → ℝ) (a b : Fin n) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * Matrix.single a b (1 : ℂ) =
      Complex.exp (((θ a - θ b : ℝ) : ℂ) * Complex.I) • (Matrix.single a b (1 : ℂ) *
        Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [mul_one, one_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp

theorem torus_weight_action : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∀ (ν : Fin (2 * r + k + 1) → ℝ) (v : R.smSub), PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) ν (v : R.H) → Formalism.REAL.IsWeight E ν v ∧ ∀ a b, PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) (ν + PI.UpqRep.root a b) ((E a b v : R.smSub) : R.H) := by
  intro hK k r ε mu R hR
  exact _root_.GlobalTheory.TorusWeight.torus_weight_action hK k r ε mu R (_root_.GlobalTheory.isDS_of_isDG hR)

end GlobalTheory.TorusWeight
end -- clump:auto
end Gp91 -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TorusWeightEigenAndRootShift =====

-- ===== clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsLowestKFiniteVectorDiscreteSeries =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsLowestKFiniteVectorDiscreteSeries", "h": "module\n\npublic import Formalism.RealPlaceAnalysis.StatementKT\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyExistsAndAny\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.KStableFiniteDimSmoothCompactRootStable\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TorusWeightEigenAndRootShift\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DominantRootSums\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowestVector

lemma lowK_eq {n : ℕ} (ε : Fin n → Bool) (mu : Fin n → ℝ) :
    PI.UpqRep.lowK ε mu = Formalism.QuantumDeterminants.lowK ε mu := rfl

theorem exists_lowest_vector : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∃ w : R.smSub, ‖w‖ = 1 ∧ R.KFin (w : R.H) ∧ Formalism.REAL.KHighest ε E (Formalism.QuantumDeterminants.lowK ε mu) w ∧ FiniteDimensional ℂ (Formalism.REAL.kSpan ε E w) := by
  intro hK k r ε mu R hR Q E hQ hE
  have hD := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R hR Q hQ
  obtain ⟨-, -, -, -, -, ⟨S, hfin, hst, -, ⟨v, hvS, hv0, hvw⟩, hmax⟩, -⟩ := hD
  rw [lowK_eq] at hvw hmax
  obtain ⟨hS1, hS2⟩ := _root_.Gp91.GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r ε mu R hR Q hQ S hfin hst
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  set u : R.H := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hu
  have huS : u ∈ S := S.smul_mem _ hvS
  have huw : PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) (Formalism.QuantumDeterminants.lowK ε mu) u := by
    intro θ hθ
    have := hvw θ hθ
    simp only at this ⊢
    rw [hu, map_smul, this, smul_comm]
  let w : R.smSub := ⟨u, (hS1 u huS).2⟩
  obtain ⟨hw1, hw2⟩ := _root_.Gp91.GlobalTheory.TorusWeight.torus_weight_action hK k r ε mu R hR Q E hQ hE (Formalism.QuantumDeterminants.lowK ε mu) w huw
  refine ⟨w, ?_, (hS1 u huS).1, ⟨hw1, ?_⟩, ?_⟩
  · show ‖u‖ = 1
    rw [hu, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  · intro a b hab he
    by_contra h0
    have hmem : ((E a b w : R.smSub) : R.H) ∈ S := by
      rw [hE a b w]; exact hS2 a b he u huS
    have h0' : ((E a b w : R.smSub) : R.H) ≠ 0 := fun h => h0 (Subtype.ext h)
    exact GlobalTheory.DominantRootSums.not_cDom_add_root _ ε _ a b hab (hmax _ _ hmem h0' (hw2 a b))
  · have hle : Formalism.REAL.kSpan ε E w ≤ S.comap R.smSub.subtype := by
      refine sInf_le ⟨huS, ?_⟩
      intro a b he x hx
      show ((E a b x : R.smSub) : R.H) ∈ S
      rw [hE a b x]; exact hS2 a b he _ hx
    have : FiniteDimensional ℂ (S.comap R.smSub.subtype) :=
      FiniteDimensional.of_injective
        ((R.smSub.subtype.comp (S.comap R.smSub.subtype).subtype).codRestrict S (fun x => x.2))
        (fun x y h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h'))
    exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.LowestVector
end -- clump:auto
end Gp91 -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsLowestKFiniteVectorDiscreteSeries =====

-- ===== clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsLowestKFiniteVectorDiscreteSeriesStatement =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsLowestKFiniteVectorDiscreteSeriesStatement", "h": "module\n\npublic import Formalism.RealPlaceAnalysis.StatementKT\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG\npublic import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsLowestKFiniteVectorDiscreteSeries\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∃ w : R.smSub, ‖w‖ = 1 ∧ R.KFin (w : R.H) ∧ Formalism.REAL.KHighest ε E (Formalism.QuantumDeterminants.lowK ε mu) w ∧ FiniteDimensional ℂ (Formalism.REAL.kSpan ε E w) := by
  first | exact @GlobalTheory.LowestVector.exists_lowest_vector
end Gp91 -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsLowestKFiniteVectorDiscreteSeriesStatement =====
