module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle758
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle184
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle172
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle757
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle762
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle662
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle588
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle761
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle748
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle760
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle736
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle745
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle735
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.EtBasis

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_ne_zero (x : ℤ_[l]) (hx : x ≠ 0) : algebraMap ℤ_[l] (WCb l) x ≠ 0 := by
  rw [PadicInt.unitCoeff_spec hx, map_mul, map_pow, map_natCast]
  exact mul_ne_zero ((PadicInt.unitCoeff hx).isUnit.map _).ne_zero
    (pow_ne_zero _ (WittVector.irreducible l).ne_zero)

theorem algebraMap_mem_OE {K : FinExt l} (bk : BK K) (x : ℤ_[l]) : algebraMap ℤ_[l] (WCb l) x ∈ bk.OE := by
  intro n
  obtain ⟨y, hy⟩ := (Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x))
  refine ⟨0, (PadicInt.appr x n : bk.S), algebraMap ℤ_[l] (WCb l) y, ?_⟩
  have : x = (PadicInt.appr x n : ℤ_[l]) + (l : ℤ_[l]) ^ n * y := by rw [mul_comm, hy]; ring
  have h2 := congrArg (algebraMap ℤ_[l] (WCb l)) this
  rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast] at h2
  rw [pow_zero, one_mul, h2, map_natCast]

theorem evW_mem_OE {K : FinExt l} (bk : BK K) (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem not_l_dvd_E {K : FinExt l} (bk : BK K) : ¬ (l : bk.S) ∣ bk.E := by
  rintro ⟨t, ht⟩
  have h := congrArg (coeff bk.Ep.natDegree) ht
  rw [← map_natCast (C (R := Wq l bk.a)) l, coeff_C_mul, Polynomial.coeff_coe, bk.monic.coeff_natDegree] at h
  have h2 := congrArg (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) h
  rw [map_mul, map_natCast, map_one, CharP.cast_eq_zero, zero_mul] at h2
  exact one_ne_zero h2

theorem adj_comm {d : ℕ} (f A B : Matrix (Fin d) (Fin d) ℤ_[l]) (hf : f.det ≠ 0) (h : f * B = A * f) :
    f.adjugate * A = B * f.adjugate := by
  have h1 : f.det • (f.adjugate * A) = f.det • (B * f.adjugate) := by
    calc f.det • (f.adjugate * A) = f.adjugate * A * (f * f.adjugate) := by
          rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
      _ = f.adjugate * (f * B) * f.adjugate := by rw [h]; simp only [Matrix.mul_assoc]
      _ = f.det • (B * f.adjugate) := by
          rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
  exact smul_right_injective _ hf h1

end GlobalTheory.EtBasis

namespace GlobalTheory.EtBasis

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ'' : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (F : Pre bk N d ρ) (f : Matrix (Fin d) (Fin d) (ℤ_[l])), f.det ≠ 0 → (∀ g, IsUnit (ρ'' g)) →
    (∀ g, f * ρ'' g = ρ g * f) → ∃ T'' P : Matrix (Fin d) (Fin d) (WCb l), IsUnit T'' ∧ (∀ i j, P i j ∈ bk.OE) ∧
      zW f * T'' = F.T * P := by
  intro l _ K bk τ _ N d ρ ρ'' F f hf hρ'' hfρ
  obtain ⟨hsat1, -, hinvS, -, -, hgalOE, hfrobOE⟩ := GlobalTheory.T.integral_elements_unit_factorization l K bk
  have hl0 : (l : WCb l) ≠ 0 := (WittVector.irreducible l).ne_zero
  have hzW : ∀ M : Matrix (Fin d) (Fin d) ℤ_[l], zW M = (algebraMap ℤ_[l] (WCb l)).mapMatrix M := fun _ => rfl
  have hzWmul : ∀ M M' : Matrix (Fin d) (Fin d) ℤ_[l], zW (M * M') = zW M * zW M' := fun M M' => by
    rw [hzW, hzW, hzW, map_mul]
  have hfadj : zW f * zW f.adjugate = algebraMap ℤ_[l] (WCb l) f.det • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← hzWmul, Matrix.mul_adjugate]
    ext i j
    by_cases h : i = j <;> simp [zW, h, Matrix.one_apply]
  have hTdet : F.T.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 F.unit).ne_zero
  have hdf : algebraMap ℤ_[l] (WCb l) f.det ≠ 0 := algebraMap_ne_zero _ hf
  set Y1 := zW f.adjugate * F.T with hY1
  have hY1det : Y1.det ≠ 0 := by
    rw [hY1, Matrix.det_mul, hzW, ← RingHom.map_det, Matrix.det_adjugate, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hdf) hTdet
  obtain ⟨m, P₀, Y', hP₀, hP₀det, hY', hlat, hsat⟩ := GlobalTheory.SatLattice.exists_lattice_basis l K bk d Y1 hY1det
  have hlm : (l : WCb l) ^ m ≠ 0 := pow_ne_zero _ hl0
  have hcancel : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (l : WCb l) ^ m • M = (l : WCb l) ^ m • M' → M = M' :=
    fun M M' h => Matrix.ext fun i j => mul_left_cancel₀ hlm (congrFun (congrFun h i) j)

  have hY'det : Y'.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hY'
    rw [Matrix.det_smul, h0, mul_zero, Matrix.det_mul] at this
    exact mul_ne_zero hY1det hP₀det this.symm

  obtain ⟨e, he, hEe⟩ := hinvS bk.E (not_l_dvd_E bk)
  have hφ : ∃ A'' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A'' i j ∈ bk.OE) ∧ Y'.map (frobW l) = Y' * A'' := by
    set B := e ^ N • F.A.map bk.evW with hB
    have hB_OE : ∀ i j, B i j ∈ bk.OE := fun i j => by
      simp only [hB, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      exact bk.OE.mul_mem (bk.OE.pow_mem he N) (evW_mem_OE bk _)
    have hTφ : F.T.map (frobW l) = F.T * B := by
      have h := congrArg (fun M => e ^ N • M) F.φ
      have h1 : e ^ N * bk.evW bk.E ^ N = 1 := by rw [← mul_pow, mul_comm, hEe, one_pow]
      simp only [smul_smul, h1, one_smul] at h
      rw [h, hB, Matrix.mul_smul]
    have hfrobzW : ∀ M : Matrix (Fin d) (Fin d) ℤ_[l], (zW M).map (frobW l) = zW M := fun M => by
      exact Matrix.ext fun i j => (frobW l).commutes _
    have hmapmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l),
        (M * M').map (frobW l) = M.map (frobW l) * M'.map (frobW l) :=
      fun M M' => Matrix.map_mul (f := (frobW l).toRingHom)
    have hY1φ : Y1.map (frobW l) = Y1 * B := by
      rw [hY1, hmapmul, hfrobzW, hTφ, Matrix.mul_assoc]
    set V := B * P₀.map (frobW l) with hV
    have hV_OE : ∀ i j, V i j ∈ bk.OE := fun i j => by
      simp only [hV, Matrix.mul_apply]
      exact bk.OE.sum_mem fun k _ => bk.OE.mul_mem (hB_OE i k) (hfrobOE _ (hP₀ k j))
    have hmain : (l : WCb l) ^ m • Y'.map (frobW l) = Y1 * V := by
      have h : ((l : WCb l) ^ m • Y').map (frobW l) = (Y1 * P₀).map (frobW l) := by rw [hY']
      rw [hmapmul, hY1φ] at h
      rw [hV, ← Matrix.mul_assoc, ← h]
      ext i j
      simp [map_mul, map_pow, map_natCast]
    have hcol : ∀ j, ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => V i j) = P₀ *ᵥ w := by
      intro j
      obtain ⟨w, hw, hvw⟩ := hlat (fun i => V i j) (fun i => hV_OE i j) m (fun i => by
        have : (Y1 *ᵥ fun i => V i j) i = (Y1 * V) i j := by
          simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
        rw [this, ← hmain, Matrix.smul_apply, smul_eq_mul]
        exact Dvd.intro _ rfl)
      exact ⟨w, hw, funext fun i => mul_left_cancel₀ hlm (congrFun hvw i)⟩
    choose w hw hvw using hcol
    refine ⟨Matrix.of fun i j => w j i, fun i j => hw j i, ?_⟩
    have hVP : V = P₀ * Matrix.of fun i j => w j i := by
      ext i j
      have := congrFun (hvw j) i
      simp only [Matrix.mulVec, dotProduct] at this
      simp [Matrix.mul_apply, this]
    apply hcancel
    rw [hmain, hVP, ← Matrix.mul_assoc, ← hY', Matrix.smul_mul]

  have hg : ∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (WCb l), IsUnit R ∧
      R * Y'.map (galW l (g : GQ l)) = Y' := by
    intro g hfix
    refine ⟨zW (ρ'' g), by rw [hzW]; exact (hρ'' g).map _, ?_⟩
    have hgmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (M * M').map (galW l (g : GQ l)) =
        M.map (galW l (g : GQ l)) * M'.map (galW l (g : GQ l)) :=
      fun M M' => Matrix.map_mul (f := (galW l (g : GQ l)).toRingEquiv.toRingHom)
    have hgzW : ∀ M : Matrix (Fin d) (Fin d) ℤ_[l], (zW M).map (galW l (g : GQ l)) = zW M := fun M => by
      exact Matrix.ext fun i j => (galW l (g : GQ l)).commutes _
    have hgP : P₀.map (galW l (g : GQ l)) = P₀ := by
      exact Matrix.ext fun i j => hgalOE g hfix _ (hP₀ i j)
    have hcomm : zW (ρ'' g) * zW f.adjugate = zW f.adjugate * zW (ρ g) := by
      rw [← hzWmul, ← hzWmul, adj_comm f (ρ g) (ρ'' g) hf (hfρ g)]
    have h : ((l : WCb l) ^ m • Y').map (galW l (g : GQ l)) = (Y1 * P₀).map (galW l (g : GQ l)) := by rw [hY']
    rw [hgmul, hY1, hgmul, hgzW, hgP] at h
    have hs : ((l : WCb l) ^ m • Y').map (galW l (g : GQ l)) = (l : WCb l) ^ m • Y'.map (galW l (g : GQ l)) := by
      ext i j; simp
    apply hcancel
    rw [← Matrix.mul_smul, ← hs, h, hY', hY1]
    calc zW (ρ'' g) * (zW f.adjugate * F.T.map (galW l (g : GQ l)) * P₀)
        = zW (ρ'' g) * zW f.adjugate * F.T.map (galW l (g : GQ l)) * P₀ := by simp only [Matrix.mul_assoc]
      _ = zW f.adjugate * (zW (ρ g) * F.T.map (galW l (g : GQ l))) * P₀ := by
          rw [hcomm]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [F.fix g hfix]
  obtain ⟨A'', hA'', hφ'⟩ := hφ
  have hunit : IsUnit Y' := GlobalTheory.SatInvUnit.isUnit_of_saturated l K bk d Y' A'' hY'det hA'' hφ' hg hsat
  set Ti := F.T⁻¹ with hTi'
  have hTi : Ti * F.T = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 F.unit)
  have hTTi : F.T * Ti = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 F.unit)
  refine ⟨Y', Ti * zW f * Y', hunit, fun i j => ?_, ?_⟩
  · have hP : (l : WCb l) ^ m • (Ti * zW f * Y') = algebraMap ℤ_[l] (WCb l) f.det • P₀ := by
      rw [← Matrix.mul_smul, hY', hY1]
      calc Ti * zW f * (zW f.adjugate * F.T * P₀) = Ti * (zW f * zW f.adjugate) * F.T * P₀ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [hfadj, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul, hTi, Matrix.one_mul]
    have := congrFun (congrFun hP i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    refine GlobalTheory.SatLattice.sat_pow bk.OE hl0 hsat1 m _ ?_
    rw [this]
    exact bk.OE.mul_mem (algebraMap_mem_OE bk _) (hP₀ i j)
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hTTi, Matrix.one_mul]

end GlobalTheory.EtBasis
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim



theorem mittagLeffler_approx : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), IsUnit T0 → (∀ n i j, R n i j ∈ bk.OE) → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (tw.d' n) → bk.S, ∃ s' : Fin (tw.d' m) → bk.S, ∀ i, (l : WCb l) ^ n ∣ ((R n *ᵥ fun j => bk.evW (X ^ c * s j)) - R m *ᵥ fun j => bk.evW (s' j)) i := by
  intro l _ K bk τ hτ d N ρ tw F T0 R hT0 hR hRF n
  set I : Ideal (WCb l) := Ideal.span {(l : WCb l) ^ n} with hI
  let q : WCb l →+* WCb l ⧸ I := Ideal.Quotient.mk I
  have hq : ∀ w, (l : WCb l) ^ n ∣ w ↔ q w = 0 := fun w => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  have hmat : ∀ {a b : ℕ} (A B : Matrix (Fin a) (Fin b) (WCb l)), (∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) →
      A.map q = B.map q := by
    intro a b A B h
    ext i j
    simp only [Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub]
    exact (hq _).1 (h i j)
  have hvec : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) (WCb l)) (v : Fin b → WCb l),
      (fun i => q ((M *ᵥ v) i)) = M.map q *ᵥ fun j => q (v j) := fun M v => funext fun i => RingHom.map_mulVec q M v i
  obtain ⟨c, y, hcy⟩ := GlobalTheory.BKLim.flatPow_dvd_perPow_mod l K bk τ hτ (2 * N) n
  refine ⟨c, fun m hnm s => ?_⟩

  obtain ⟨Yn, Y'n, hYn, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N (tw.d' n) _ (F n)
  obtain ⟨Ym, Y'm, hYm, hYYm⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N (tw.d' m) _ (F m)
  obtain ⟨Sm, hSm⟩ := (tw.onto m).surj
  have hu : IsUnit (inclW l τ ^ N) := (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).1.pow N

  have hTY : (F m).T * Y'm.map (inclW l) = inclW l τ ^ N • (1 : Matrix _ _ (WCb l)) := by
    have h1 : (Ym * Y'm).map (inclW l) = (τ ^ (2 * N) • (1 : Matrix _ _ (Ainf l))).map (inclW l) := by rw [hYYm]
    rw [Matrix.map_mul, hYm] at h1
    have h2 : (τ ^ (2 * N) • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (Ainf l))).map (inclW l) =
        inclW l τ ^ N • (inclW l τ ^ N • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (WCb l))) := by
      rw [smul_smul, ← pow_add, ← two_mul, ← map_pow]
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [← hu.smul_left_cancel, ← Matrix.smul_mul, h1, h2]
  let qi : Ainf l →+* WCb l ⧸ I := q.comp (inclW l)
  have hv : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) (Ainf l)) (v : Fin b → Ainf l),
      (fun i => qi ((M *ᵥ v) i)) = M.map qi *ᵥ fun j => qi (v j) := fun M v => funext fun i => RingHom.map_mulVec qi M v i
  have hzq : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℤ_[l]),
      (M.map (algebraMap ℤ_[l] (Ainf l))).map qi = (zW M).map q := fun M => by
    ext i j
    show q (inclW l (algebraMap ℤ_[l] (Ainf l) (M i j))) = q (algebraMap ℤ_[l] (WCb l) (M i j))
    congr 1
    exact (inclWA l).commutes _

  have F1 : T0.map q * (R n).map q = (zW (tw.Pi n)).map q * (F n).T.map q := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact (hmat _ _ fun i j => by rw [Matrix.sub_apply, dvd_sub_comm, ← Matrix.sub_apply]; exact hRF n i j)
  have F2 : T0.map q * (R m).map q = (zW (tw.Pi m)).map q * (F m).T.map q := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact (hmat _ _ fun i j => by
      rw [Matrix.sub_apply, dvd_sub_comm, ← Matrix.sub_apply]; exact dvd_trans (pow_dvd_pow _ hnm) (hRF m i j))
  have F3 : (zW (tw.Pi m)).map q * (zW Sm).map q = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_one q (map_zero q) (map_one q)]
    refine hmat _ _ fun i j => dvd_trans (pow_dvd_pow _ hnm) ?_
    have h := map_dvd (algebraMap ℤ_[l] (WCb l)) (hSm i j)
    rw [map_pow, map_natCast] at h
    convert h using 1
    rw [← Matrix.map_mul, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have F4 : Yn.map qi = qi τ ^ N • (F n).T.map q := by
    have : Yn.map qi = (Yn.map (inclW l)).map q := by ext i j; rfl
    rw [this, hYn]; ext i j; simp [qi]
  have F5 : (F m).T.map q * Y'm.map qi = qi τ ^ N • (1 : Matrix _ _ (WCb l ⧸ I)) := by
    have : Y'm.map qi = (Y'm.map (inclW l)).map q := by ext i j; rfl
    rw [this, ← Matrix.map_mul, hTY]
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp [qi]
  have hXc : q (inclW l (bk.ev X ^ c)) = qi τ ^ (2 * N) * qi y := by
    have h0 : (l : WCb l) ^ n ∣ inclW l (bk.ev X ^ c - τ ^ (2 * N) * y) := by
      have := map_dvd (inclW l) hcy
      rwa [map_pow, map_natCast] at this
    have h := (hq _).1 h0
    rw [map_sub, map_sub, sub_eq_zero] at h
    rw [h]
    simp [qi]
  have F6 : (fun j => q (bk.evW (X ^ c * s j))) = (qi τ ^ (2 * N) * qi y) • fun j => qi (bk.ev (s j)) := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul, ← hXc]
    show q (inclW l (bk.ev (X ^ c * s j))) = q (inclW l (bk.ev X ^ c)) * q (inclW l (bk.ev (s j)))
    rw [map_mul, map_pow, map_mul, map_mul]

  set e : Fin (tw.d' n) → WCb l ⧸ I := fun j => qi (bk.ev (s j)) with he
  set zA := algebraMap ℤ_[l] (Ainf l) with hzA
  set w1 : Fin (tw.d' m) → Ainf l := (Sm.map zA) *ᵥ ((tw.Pi n).map zA *ᵥ (Yn *ᵥ fun j => bk.ev (s j))) with hw1
  set a : Fin (tw.d' m) → Ainf l := y • (Y'm *ᵥ w1) with ha
  have hqa : (fun j => q (inclW l (a j))) =
      qi y • (Y'm.map qi *ᵥ ((zW Sm).map q *ᵥ ((zW (tw.Pi n)).map q *ᵥ (Yn.map qi *ᵥ e)))) := by
    have h0 : (fun j => q (inclW l (a j))) = qi y • fun j => qi ((Y'm *ᵥ w1) j) := by
      funext j
      simp only [ha, Pi.smul_apply, smul_eq_mul, map_mul]
      rfl
    rw [h0, hv, hw1, hv, hv, hv, hzq, hzq]
  obtain ⟨T0i, hT0i⟩ := (hT0.map (RingHom.mapMatrix q)).exists_left_inv
  have hT0i' : T0i * T0.map q = 1 := hT0i
  have G : (R n).map q *ᵥ ((qi τ ^ (2 * N) * qi y) • e) =
      (R m).map q *ᵥ (qi y • (Y'm.map qi *ᵥ ((zW Sm).map q *ᵥ ((zW (tw.Pi n)).map q *ᵥ (Yn.map qi *ᵥ e))))) := by
    have canc : ∀ u v : Fin d → WCb l ⧸ I, T0.map q *ᵥ u = T0.map q *ᵥ v → u = v := fun u v h => by
      have := congrArg (fun x => T0i *ᵥ x) h
      simpa only [Matrix.mulVec_mulVec, hT0i', Matrix.one_mulVec] using this
    apply canc
    have L : T0.map q *ᵥ ((R n).map q *ᵥ ((qi τ ^ (2 * N) * qi y) • e)) =
        (qi τ ^ (2 * N) * qi y) • (((zW (tw.Pi n)).map q * (F n).T.map q) *ᵥ e) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, F1]
    have Rr : T0.map q *ᵥ ((R m).map q *ᵥ (qi y • (Y'm.map qi *ᵥ ((zW Sm).map q *ᵥ ((zW (tw.Pi n)).map q *ᵥ (Yn.map qi *ᵥ e)))))) =
        (qi y * qi τ ^ N * qi τ ^ N) • (((zW (tw.Pi n)).map q * (F n).T.map q) *ᵥ e) := by
      simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
      rw [F2, Matrix.mul_assoc ((zW (tw.Pi m)).map q), F5, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.smul_mul, F3, Matrix.one_mul, F4]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mulVec, smul_smul]
      first | rfl | (congr 1; ring)
    rw [L, Rr]
    congr 1
    ring
  have hev : ∀ t : bk.S, bk.evW t ∈ bk.OE := fun t => by
    intro k
    exact ⟨0, t, 0, by simp⟩
  have hxOE : ∀ i, (R n *ᵥ fun j => bk.evW (X ^ c * s j)) i ∈ bk.OE := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hR n i j) (hev _)
  obtain ⟨s', hs'⟩ := GlobalTheory.T.breuilKisin_descent_coefficients_ainf_mod_pow l K bk d (tw.d' m) n (R m) (R n *ᵥ fun j => bk.evW (X ^ c * s j)) a (hR m) hxOE
    (fun i => by
      rw [hq, Pi.sub_apply, map_sub, sub_eq_zero]
      have h1 : q ((R n *ᵥ fun j => bk.evW (X ^ c * s j)) i) =
          ((R n).map q *ᵥ fun j => q (bk.evW (X ^ c * s j))) i := congrFun (hvec (R n) fun j => bk.evW (X ^ c * s j)) i
      have h2 : q ((R m *ᵥ fun j => inclW l (a j)) i) = ((R m).map q *ᵥ fun j => q (inclW l (a j))) i :=
        congrFun (hvec (R m) fun j => inclW l (a j)) i
      rw [h1, h2, F6, hqa, G])
  exact ⟨s', hs'⟩

end GlobalTheory.BKLim
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isCrys_of_crystallineBreuilKisinFrame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val), F.IsCr → IsCrys (P.PD K) (qRep ρ) := by
  first | (exact @GlobalTheory.CrTop.crys_of_frame) | (exact GlobalTheory.CrTop.crys_of_frame) | (intros; apply GlobalTheory.CrTop.crys_of_frame  <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.CuspKillProof

theorem cuspKill_holds : ∀ D : D7, CuspKill D := by
  intro D W ν hν s I hI Γ hΓQ hNΓ hnorm 𝓓 h𝓓 Φ φ hΦc hΦΓ hΦN hφ hcusp hint
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W
  haveI : BorelSpace (GA D W) := ⟨rfl⟩
  haveI : Countable (GQ W) := GlobalTheory.AutomorphicL2Unitary.countable_of_discrete
  haveI : Countable Γ := Function.Injective.countable (Subgroup.inclusion_injective hΓQ)
  have hNc : IsClosed (NI W I : Set (GA D W)) := by
    rw [← GlobalTheory.Cusp.NA_frameFlag hI]
    haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
    exact GlobalTheory.Cusp.IsoFlag.isClosed_unip _ _ _
  have hcc : GlobalTheory.Cusp.Cocompact (GQ W) (NI W I) := by
    rw [← GlobalTheory.Cusp.NA_frameFlag hI]
    exact GlobalTheory.Cusp.cocompact_single _
  haveI : LocallyCompactSpace (NI W I) := hNc.locallyCompactSpace
  have hsub : Γ.subgroupOf (NI W I) = (GQ W).subgroupOf (NI W I) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => hΓQ h, fun h => hNΓ ⟨x.2, h⟩⟩
  set κ : Measure (NI W I) := Measure.haar
  set 𝓝 : Set (NI W I) := GlobalTheory.AutomorphicL2Unitary.stdDom ((GQ W).subgroupOf (NI W I))
  have h𝓝Q : IsFundamentalDomain ((GQ W).subgroupOf (NI W I)) 𝓝 κ := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ κ
  have h𝓝Γ : IsFundamentalDomain (Γ.subgroupOf (NI W I)) 𝓝 κ := by rw [hsub]; exact h𝓝Q
  have h𝓝t : κ 𝓝 ≠ ⊤ := hcc.measure_ne_top h𝓝Q
  have h0 : ∀ g, ∫ n in 𝓝, φ ((n : GA D W) * g) ∂κ = 0 := hcusp s I hI κ 𝓝 inferInstance h𝓝Q
  exact GlobalTheory.UnfoldNormal.unfold_zero_mean (GA D W) ν Γ (NI W I) inferInstance hNc hnorm κ 𝓝 inferInstance h𝓝Γ h𝓝t
    Φ φ hΦc.measurable hφ.cont.measurable hΦN hΦΓ (fun γ hγ g => hφ.left γ (hΓQ hγ) g) h0 𝓓 h𝓓 hint

end GlobalTheory.CuspKillProof
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.doubledLagrangian_term_depends_only_on_isotropic_means : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), IsLagFrame W Y C → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ f₁ f₁' f₂ : WO V W → ℂ, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₁' → IsThetaFunO ψ V W f₂ → (∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, f₁ (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f₁' (HMul.hMul (I.map (incA D)) y + x) ∂ν) → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C f₁' f₂ := by
  first | exact @GlobalTheory.LagMeans.lagTerm_eq_of_means | exact GlobalTheory.LagMeans.lagTerm_eq_of_means | (intros; apply GlobalTheory.LagMeans.lagTerm_eq_of_means <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.doubled_lagrangian_term_frame_independent : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → IsStdChar D ψ (-1) → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (Y : Lag W) C C', IsLagFrame W Y C → IsLagFrame W Y C' → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C' f₁ f₂ := by
  first | exact @GlobalTheory.RawLift.lagTerm_frame_indep | exact GlobalTheory.RawLift.lagTerm_frame_indep | (intros; apply GlobalTheory.RawLift.lagTerm_frame_indep <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem per_ne_zero {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) {τ : Ainf l} (h : bk.IsPer τ) : τ ≠ 0 := by
  rintro rfl
  obtain ⟨-, ε, η, hε, hφ⟩ := h
  rw [map_zero] at hφ
  have h1 : WittVector.teichmuller l ε - 1 = 0 := (Units.mul_right_eq_zero η).1 hφ.symm
  have h2 : ε = 1 := by
    have := congrArg (fun w => WittVector.coeff w 0) (sub_eq_zero.1 h1)
    simpa using this
  subst h2
  exact hε.2 (by simp)

theorem iA_per_mem_nonZeroDivisors : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l),
    bk.IsPer τ → bk.iA τ ∈ nonZeroDivisors (bk.DA bk.ρ₀) := by
  intro l _ K bk τ hτ
  obtain ⟨h0, h1, -, -⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk (Ainf l) bk.ev
  haveI : IsDomain (bk.DA bk.ρ₀) := (discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [← map_zero bk.iA]
  exact fun h => per_ne_zero bk hτ (hinj h)

end GlobalTheory.BSP
end
