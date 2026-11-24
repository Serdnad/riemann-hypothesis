module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusInverseMatrix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixRelationDiscrete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedOfPhiEquationDisc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedPeriodsDiscAinf
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrobeniusOfScaledInverse, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDiscCoefficientRecurrence, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedSemistablePeriodsNullFamily

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrobeniusOfScaledInverse =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrobeniusOfScaledInverse", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBounds\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZero\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusInverseMatrix\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixRelationDiscrete\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT\nimport Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic\nimport Formalism.SharpRestriction.LevelLetterCocycles.LocCoh\n\n"}
section -- clump:auto
@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem GlobalTheory.BKLim.wseed_frob_inverse : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS * s.W'.map Φ = (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) * bk.iS bk.E ^ (2 * s.N)) • s.W' := by
  intro l _ K bk τ hτ d ρ hρ s Φ hΦ
  obtain ⟨h0, h1⟩ := GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.radius_mem l K bk
  haveI := (_root_.GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  have hτ0 := (_root_.GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).2.1
  refine GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.frob_inverse Φ s.W s.W' _ (bk.iA τ ^ (2 * s.N)) _ _ (pow_ne_zero _ hτ0) s.W_mul
    (_root_.GlobalTheory.BKLim.WSeed.crystallineDiscPeriods_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ) ?_
  have h2 : Φ (bk.iA τ) = bk.iS bk.E * bk.iA τ := by
    have h3 := hΦ.ext τ
    rw [hτ.1, map_mul] at h3
    exact h3
  rw [map_pow, h2, mul_pow]
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrobeniusOfScaledInverse =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDiscCoefficientRecurrence =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDiscCoefficientRecurrence", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBounds\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasis\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixRelationDiscrete\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrobeniusOfScaledInverse\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT\nimport Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic\nimport Formalism.SharpRestriction.LevelLetterCocycles.LocCoh\nimport Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedPeriodsDiscAinf\n\n"}
section -- clump:auto
@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem wseed_coeff_recurrence : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → ∀ (cD : ι → (bk.DA bk.ρ₀ →+ bk.DS bk.ρ₀)), (∀ i a, cD i (bk.iA a) = toDisc l (X : bk.S) bk.ρ₀ (TB.c i a)) → (∀ i x y, cD i (j x * y) = x * cD i y) → (∀ y, HasSum (fun i => j (cD i y) * bk.iA (TB.b i)) y) → (∀ i y, ‖cD i y‖ ≤ ‖y‖) → ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ∀ (i₁ : ι) (a b : Fin d), HasSum (fun i => Φ ((s.W * (s.W'.map (cD i)).map j) a b) * bk.iS (TB.c i₁ (WittVector.frobenius (TB.b i)))) (bk.iS bk.E ^ (2 * s.N) * (s.W * (s.W'.map (cD i₁)).map j) a b) := by
  intro l _ K bk τ hτ d ρ hρ s ι TB j hj cD hc hcm hsum hnorm Φ hΦ i₁ a b
  have h0 := GlobalTheory.BSP.BK.ρ₀_pos' bk
  have h1 := GlobalTheory.BSP.seedRec_ρ₀_lt_one bk
  obtain ⟨hdom, -, -⟩ := GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1
  let ΦS := Disc.map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := (X : bk.S)) (ρ' := bk.ρ₀)
    (frobS l bk.a) (GlobalTheory.BSP.seedRec_frobS_norm bk)
  have hΦS : IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) ΦS := isDiscMap_map _ _
  have hcomm : ∀ x, Φ (j x) = j (ΦS x) := GlobalTheory.BSP.seedRec_comm bk j hj Φ hΦ ΦS hΦS
  have hjS : ∀ t, j (toDisc l (X : bk.S) bk.ρ₀ t) = bk.iS t := fun t => hj.ext t
  have hΦA : ∀ x, Φ (bk.iA x) = bk.iA (WittVector.frobenius x) := fun x => hΦ.ext x
  have hcont : ∀ i, Continuous (cD i) := fun i =>
    AddMonoidHomClass.continuous_of_bound (cD i) 1 (fun y => by rw [one_mul]; exact hnorm i y)
  have hΦc : Continuous Φ :=
    AddMonoidHomClass.continuous_of_bound Φ 1 (fun y => by rw [one_mul]; exact hΦ.norm_le y)
  have hjc : Continuous j :=
    AddMonoidHomClass.continuous_of_bound j 1 (fun y => by rw [one_mul]; exact hj.norm_le y)
  let c : ι → bk.DA bk.ρ₀ := fun i => bk.iS (TB.c i₁ (WittVector.frobenius (TB.b i)))
  let L : bk.DA bk.ρ₀ →+ bk.DA bk.ρ₀ := (j : bk.DS bk.ρ₀ →+ bk.DA bk.ρ₀).comp (cD i₁)
  have hLa : ∀ y, L y = j (cD i₁ y) := fun y => rfl
  have hLc : Continuous L := hjc.comp (hcont i₁)
  have hL : ∀ t y, L (bk.iS t * y) = bk.iS t * L y := by
    intro t y
    rw [hLa, hLa, ← hjS, hcm, map_mul]
  have key : ∀ y, HasSum (fun i => Φ (j (cD i y)) * c i) (L (Φ y)) := by
    intro y
    have h := ((hsum y).map (Φ : bk.DA bk.ρ₀ →+ bk.DA bk.ρ₀) hΦc).map L hLc
    convert (preTransparency := .reducible) h using 1
    · funext i
      simp only [Function.comp_apply, AddMonoidHom.coe_coe]
      rw [map_mul Φ, hΦA, hcomm, hLa, hcm, hc, map_mul, hjS]
    · rfl
  have stepA : HasSum (fun i => Φ ((s.W * (s.W'.map (cD i)).map j) a b) * c i)
      ((s.W.map Φ * (s.W'.map Φ).map L) a b) := by

    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul]
    refine hasSum_sum fun k _ => ?_
    simp_rw [mul_assoc]
    exact (key (s.W' k b)).mul_left (Φ (s.W a k))
  haveI := hdom
  have hphi := _root_.GlobalTheory.BKLim.WSeed.crystallineDiscPeriods_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ
  have hwp := _root_.GlobalTheory.BKLim.wseed_frob_inverse l K bk τ hτ d ρ hρ s Φ hΦ
  have hmapL : ∀ (M : Matrix (Fin d) (Fin d) bk.S) (Y : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)),
      (M.map bk.iS * Y).map L = M.map bk.iS * Y.map L := by
    intro M Y
    ext k m

    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, hL]
  have hμ : (l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N * bk.iS bk.E ^ (2 * s.N) =
      bk.iS ((l : bk.S) ^ (s.c₁ + s.c₂) * frobS l bk.a bk.E ^ s.N * bk.E ^ (2 * s.N)) := by
    simp only [map_mul, map_pow, map_natCast]
  have hBL : (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS *
      (s.W'.map Φ).map L = ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N *
        bk.iS bk.E ^ (2 * s.N)) • s.W'.map L := by
    rw [← hmapL, hwp]
    ext k m
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, smul_eq_mul, hμ, hL]
  have hWJ : s.W'.map L = (s.W'.map (cD i₁)).map j := by ext; rfl
  have heq : ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) •
      (s.W.map Φ * (s.W'.map Φ).map L) = ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) •
      (bk.iS bk.E ^ (2 * s.N) • (s.W * (s.W'.map (cD i₁)).map j)) := by
    conv_lhs => rw [← Matrix.smul_mul, hphi, Matrix.mul_assoc, hBL, Matrix.mul_smul]
    rw [smul_smul, hWJ]
  have hE0 : bk.iS (frobS l bk.a bk.E) ≠ 0 := by
    intro h
    apply GlobalTheory.BSP.seedRec_frobS_E_ne_zero bk
    apply GlobalTheory.BSP.seedRec_ev_injective bk TB
    rw [map_zero]
    apply (toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι TB bk.ρ₀ h0 h1).1
    rw [map_zero]
    exact h
  have hlam : (l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (isUnit_l_disc l (bk.ev X) bk.ρ₀).ne_zero) (pow_ne_zero _ hE0)
  have hab := congrFun (congrFun heq a) b
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at hab
  have h2 := mul_left_cancel₀ hlam hab
  rw [Matrix.smul_apply, smul_eq_mul] at h2
  rw [← h2]
  exact stepA

end GlobalTheory.BSP
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDiscCoefficientRecurrence =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedSemistablePeriodsNullFamily =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedSemistablePeriodsNullFamily", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisin\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFree\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedOfPhiEquationDisc\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedPeriodsDiscAinf\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDiscCoefficientRecurrence\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT\nimport Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic\nimport Formalism.SharpRestriction.LevelLetterCocycles.LocCoh\n\n"}
section -- clump:auto
@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem exists_bounded_periods_wseed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∃ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (k : ℕ) (v : ι → Matrix (Fin d) (Fin d) (Ainf l)) (Z : ι → Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (∀ (n : ℕ) (a b : Fin d), {i | v i a b ∉ (bk.J ^ n).map bk.ev}.Finite) ∧ (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → ∀ i, s.W * (Z i).map j = (v i).map bk.iA) ∧ ∀ a b : Fin d, HasSum (fun i => bk.iA (v i a b * TB.b i)) (bk.iA ((l : Ainf l) ^ k * τ ^ (2 * s.N) * if a = b then 1 else 0)) := by
  intro l _ K bk τ hτ d ρ hρ s
  exact _root_.GlobalTheory.BSP.exists_bounded_periods_of_mul l K bk τ hτ d s.N s.W s.W' s.W_mul (_root_.GlobalTheory.BSP.wseed_coeff_recurrence l K bk τ hτ d ρ hρ s)

end GlobalTheory.BKLim
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedSemistablePeriodsNullFamily =====
