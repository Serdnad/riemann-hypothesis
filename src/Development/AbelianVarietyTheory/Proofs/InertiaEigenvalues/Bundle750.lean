module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle588
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle705
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle736
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle564
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle731
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle661
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle042
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle330
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle518
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle737
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle739
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem topBasis_disc_regular : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → Function.Injective (toDisc l (s X) bk.ρ₀) ∧ toDisc l (s X) bk.ρ₀ (s bk.E) ∈ nonZeroDivisors (Disc l (s X) bk.ρ₀) ∧ (l : A) ∈ nonZeroDivisors A ∧ ∀ F : bk.DS bk.ρ₀ →+* Disc l (s X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) s F → Function.Injective F := by
  intro l _ K bk A _ s ι TB
  obtain ⟨h0, h1, -, -⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk A s
  refine ⟨(GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk A s ι TB bk.ρ₀ h0 h1).1, ?_, ?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have hn := (GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι TB bk.ρ₀ le_rfl h1).1 y
    rw [mul_comm, hy, norm_zero] at hn
    have hp : (0 : ℝ) < (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast h0) _
    exact norm_eq_zero.1 ((mul_eq_zero.1 hn.symm).resolve_left hp.ne')
  · have hH : IsHausdorff bk.J bk.S := bk.complete.toIsHausdorff
    have hF := GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB hH
    have hW : ((l : ℕ) : Wq l bk.a) ≠ 0 := by
      intro h
      have h2 := congrArg (fun w : Wq l bk.a => w.coeff 1) h
      simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at h2
      exact one_ne_zero h2
    have hS : ((l : ℕ) : bk.S) ≠ 0 := by
      intro h
      have h2 := congrArg (PowerSeries.constantCoeff) h
      rw [map_natCast, map_zero] at h2
      exact hW h2
    have := hF.2.2.2.2 _ (mem_nonZeroDivisors_of_ne_zero hS)
    rwa [map_natCast] at this
  · intro F hF
    obtain ⟨_, -, -, -, -, -, -, -, hnorm⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB bk.ρ₀ h0 h1 F hF
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h := hnorm x
    rw [hx, norm_zero] at h
    exact norm_eq_zero.1 h.symm

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix

theorem frob_inverse {R : Type} [CommRing R] [IsDomain R] {d : ℕ} (Φ : R →+* R)
    (W W' B : Matrix (Fin d) (Fin d) R) (t e lam : R) (ht : t ≠ 0)
    (hW : W * W' = t • (1 : Matrix (Fin d) (Fin d) R)) (hB : lam • W.map Φ = W * B) (hΦ : Φ t = e * t) :
    B * W'.map Φ = (lam * e) • W' := by
  have hdet : W.det ≠ 0 := by
    intro h
    have h1 := congrArg Matrix.det hW
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ ht h1.symm
  have h2 : W.map Φ * W'.map Φ = (e * t) • (1 : Matrix (Fin d) (Fin d) R) := by
    rw [← Matrix.map_mul, hW, ← hΦ]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have h3 : W * (B * W'.map Φ - (lam * e) • W') = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← hB, Matrix.smul_mul, h2, Matrix.mul_smul, hW, smul_smul, smul_smul,
      mul_assoc, sub_self]
  have h4 : W.det • (B * W'.map Φ - (lam * e) • W') = 0 := by
    rw [← Matrix.one_mul (B * W'.map Φ - (lam * e) • W'), ← Matrix.smul_mul, ← Matrix.adjugate_mul,
      Matrix.mul_assoc, h3, Matrix.mul_zero]
  rw [← sub_eq_zero]
  ext i j
  have h5 := congrFun (congrFun h4 i) j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h5
  exact (mul_eq_zero.1 h5).resolve_left hdet

theorem radius_mem (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have h1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have h2 : (0 : ℝ) < (bk.Ep.natDegree : ℝ) := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (lt_trans zero_lt_one h1), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg h1 (neg_lt_zero.2 (one_div_pos.2 h2))

end GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix

theorem GlobalTheory.BSP.seed_frob_inverse : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS * s.W'.map Φ = (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) * bk.iS bk.E ^ (2 * s.N)) • s.W' := by
  intro l _ K bk τ hτ d ρ hρ s Φ hΦ
  obtain ⟨h0, h1⟩ := GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.radius_mem l K bk
  haveI := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1
  have hτ0 := (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).2.1
  refine GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.frob_inverse Φ s.W s.W' _ (bk.iA τ ^ (2 * s.N)) _ _ (pow_ne_zero _ hτ0) s.W_mul
    (GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ) ?_
  have h2 : Φ (bk.iA τ) = bk.iS bk.E * bk.iA τ := by
    have h3 := hΦ.ext τ
    rw [hτ.1, map_mul] at h3
    exact h3
  rw [map_pow, h2, mul_pow]
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CoefDescent

variable {l : ℕ} [hl : Fact l.Prime]

theorem pow_dvd_of_pow_dvd_inclW (k : ℕ) (a : Ainf l) (h : ((l : ℕ) : WCb l) ^ k ∣ inclW l a) :
    ((l : ℕ) : Ainf l) ^ k ∣ a := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    obtain ⟨c, hc⟩ := h
    have h0 : a.coeff 0 = 0 := by
      have h1 : (inclW l a).coeff 0 = 0 := by
        rw [hc, pow_succ', mul_assoc]; exact coeff_zero_l_mul _
      change algebraMap (OCb l) (Cb l) (a.coeff 0) = 0 at h1
      exact (map_eq_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).1 h1
    obtain ⟨b, rfl⟩ := ainf_exists_l_mul_of_coeff_zero a h0
    have hl0 : ((l : ℕ) : WCb l) ≠ 0 := fun h => by
      have h1 := congrArg (fun x : WCb l => x.coeff 1) h
      simp [WittVector.coeff_p] at h1
    have hb : ((l : ℕ) : WCb l) ^ k ∣ inclW l b := by
      refine ⟨c, mul_left_cancel₀ hl0 ?_⟩
      rw [← mul_assoc, ← pow_succ', ← hc, map_mul, map_natCast]
    exact pow_succ' ((l : ℕ) : Ainf l) k ▸ mul_dvd_mul_left _ (ih b hb)

variable {K : FinExt l} (bk : BK K)

theorem isUnit_evW_X : IsUnit (bk.evW X) := by
  have e : bk.evW X = WittVector.teichmuller l (algebraMap (OCb l) (Cb l) bk.flat) := by
    simp [BK.evW, bk.ev_X, inclW, WittVector.map_teichmuller]
  rw [e]
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [WittVector.teichmuller_coeff_zero]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 bk.flat_ne_zero

def Approx (n M : ℕ) (w : WCb l) : Prop :=
  ∃ (s : bk.S) (y : WCb l), bk.evW X ^ M * w = bk.evW s + (l : WCb l) ^ n * y

theorem Approx.mono {n M M' : ℕ} {w : WCb l} (h : Approx bk n M w) (hM : M ≤ M') : Approx bk n M' w := by
  obtain ⟨s, y, e⟩ := h
  refine ⟨X ^ (M' - M) * s, bk.evW X ^ (M' - M) * y, ?_⟩
  have : bk.evW X ^ M' = bk.evW X ^ (M' - M) * bk.evW X ^ M := by
    rw [← pow_add, Nat.sub_add_cancel hM]
  rw [this, map_mul, map_pow]
  linear_combination bk.evW X ^ (M' - M) * e

theorem exists_approx {ι : Type} [Fintype ι] (n : ℕ) (w : ι → WCb l) (hw : ∀ i, w i ∈ bk.OE) :
    ∃ M, ∀ i, Approx bk n M (w i) := by
  classical
  choose m hm using fun i => hw i n
  refine ⟨Finset.univ.sup m, fun i => ?_⟩
  obtain ⟨s, y, e⟩ := hm i
  exact Approx.mono bk ⟨s, y, e⟩ (Finset.le_sup (Finset.mem_univ i))

theorem descent : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (WCb l)) (x : Fin d → WCb l) (a : Fin d' → Ainf l), (∀ i j, R i j ∈ bk.OE) → (∀ i, x i ∈ bk.OE) → (∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => inclW l (a j)) i) → ∃ s : Fin d' → bk.S, ∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => bk.evW (s j)) i := by
  intro l _ K bk d d' n R x a hR hx hdiv
  obtain ⟨M₁, h₁⟩ := exists_approx bk n (fun p : Fin d × Fin d' => R p.1 p.2) (fun p => hR p.1 p.2)
  obtain ⟨M₂, h₂⟩ := exists_approx bk n x hx
  obtain ⟨M, hM1, hM2⟩ : ∃ M, M₁ ≤ M ∧ M₂ ≤ M := ⟨max M₁ M₂, le_max_left _ _, le_max_right _ _⟩
  choose r yR hRe using fun i j => (h₁ (i, j)).mono bk hM1
  choose ξ z hxe using fun i => (h₂ i).mono bk hM2
  simp only at hRe
  obtain ⟨c, hc, hc1⟩ := GlobalTheory.T.exists_ainf_linear_retraction_breuilKisin l K bk
  have hcev : ∀ s : bk.S, c (bk.ev s) = s := fun s => by
    have := hc s 1; rwa [mul_one, hc1, mul_one] at this

  have hb : ∀ i, ((l : ℕ) : Ainf l) ^ n ∣ bk.ev (ξ i) - ∑ j, bk.ev (r i j) * a j := by
    intro i
    apply pow_dvd_of_pow_dvd_inclW
    obtain ⟨q, hq⟩ := hdiv i
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct] at hq
    have hs : ∑ j, bk.evW (r i j) * inclW l (a j) =
        bk.evW X ^ M * ∑ j, R i j * inclW l (a j) - (l : WCb l) ^ n * ∑ j, yR i j * inclW l (a j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      linear_combination (-(inclW l (a j))) * hRe i j
    refine ⟨bk.evW X ^ M * q - z i + ∑ j, yR i j * inclW l (a j), ?_⟩
    have e1 : inclW l (bk.ev (ξ i) - ∑ j, bk.ev (r i j) * a j) =
        bk.evW (ξ i) - ∑ j, bk.evW (r i j) * inclW l (a j) := by

      simp [BK.evW, map_sub, map_sum, map_mul]
    rw [e1, hs]
    linear_combination (-1 : WCb l) * hxe i + bk.evW X ^ M * hq
  choose b' hb' using hb
  refine ⟨fun j => c (a j), fun i => ?_⟩

  have hci : ξ i - ∑ j, r i j * c (a j) = (l : bk.S) ^ n * c (b' i) := by
    have := congrArg c (hb' i)

    rw [map_sub, map_sum, hcev] at this
    have e2 : ((l : ℕ) : Ainf l) ^ n * b' i = bk.ev ((l : bk.S) ^ n) * b' i := by
      rw [map_pow, map_natCast]
    rw [e2] at this
    simp only [hc] at this
    exact this
  have hci' := congrArg bk.evW hci

  rw [map_sub, map_sum, map_mul, map_pow, map_natCast] at hci'
  simp only [map_mul] at hci'
  have hU := (isUnit_evW_X bk).pow M
  rw [← hU.dvd_mul_left]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  have hs : bk.evW X ^ M * ∑ j, R i j * bk.evW (c (a j)) =
      ∑ j, bk.evW (r i j) * bk.evW (c (a j)) + (l : WCb l) ^ n * ∑ j, yR i j * bk.evW (c (a j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    linear_combination (bk.evW (c (a j))) * hRe i j
  refine ⟨bk.evW (c (b' i)) + z i - ∑ j, yR i j * bk.evW (c (a j)), ?_⟩
  linear_combination hxe i - hs + hci'

end GlobalTheory.CoefDescent

theorem GlobalTheory.descentCoefficients : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (WCb l)) (x : Fin d → WCb l) (a : Fin d' → Ainf l), (∀ i j, R i j ∈ bk.OE) → (∀ i, x i ∈ bk.OE) → (∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => inclW l (a j)) i) → ∃ s : Fin d' → bk.S, ∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => bk.evW (s j)) i :=
  GlobalTheory.CoefDescent.descent
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SmithOE

theorem pid_dichotomy {O : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] (d : ℕ)
    (P : Matrix (Fin d) (Fin d) O) :
    ∃ U W : Matrix (Fin d) (Fin d) O, W * U = 1 ∧ U * W = 1 ∧
      ∀ j, (∃ w : Fin d → O, (fun i => U i j) = P *ᵥ w) ∨ (∀ k, ¬ IsUnit ((W * P) j k)) := by
  classical
  obtain ⟨n, snf⟩ := (LinearMap.range (Matrix.mulVecLin P)).smithNormalForm (Pi.basisFun O (Fin d))
  set U : Matrix (Fin d) (Fin d) O := (Pi.basisFun O (Fin d)).toMatrix snf.bM with hUdef
  set W : Matrix (Fin d) (Fin d) O := snf.bM.toMatrix (Pi.basisFun O (Fin d)) with hWdef
  have hWU : W * U = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hUW : U * W = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  refine ⟨U, W, hWU, hUW, fun j => ?_⟩
  have hUcol : (fun i => U i j) = (snf.bM j : Fin d → O) := by
    funext i
    simp [hUdef, Module.Basis.toMatrix_apply]
  have hmem : ∀ k, (fun i => P i k) ∈ LinearMap.range (Matrix.mulVecLin P) := fun k =>
    ⟨Pi.single k 1, by funext i; simp⟩
  have hWP : ∀ k, (W * P) j k = snf.bM.repr (fun i => P i k) j := by
    intro k
    have h := Module.Basis.toMatrix_mulVec_repr (Pi.basisFun O (Fin d)) snf.bM (fun i => P i k)
    rw [← h, ← hWdef]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  by_cases h : ∃ i, snf.f i = j ∧ IsUnit (snf.a i)
  · obtain ⟨i, rfl, u, hu⟩ := h
    left
    have hN : (snf.bM (snf.f i) : Fin d → O) ∈ LinearMap.range (Matrix.mulVecLin P) := by
      have h1 : (snf.bM (snf.f i) : Fin d → O) = (↑u⁻¹ : O) • (snf.bN i : Fin d → O) := by
        rw [snf.snf, ← hu, smul_smul, Units.inv_mul, one_smul]
      rw [h1]
      exact Submodule.smul_mem _ _ (snf.bN i).2
    obtain ⟨w, hw⟩ := hN
    exact ⟨w, by rw [hUcol, ← hw]; rfl⟩
  · right
    intro k
    rw [hWP k]
    by_cases hj : j ∈ Set.range snf.f
    · obtain ⟨i, rfl⟩ := hj
      have h2 := congrFun (snf.repr_comp_embedding_eq_smul ⟨_, hmem k⟩) i
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h2
      have h3 : snf.bM.repr (fun i => P i k) (snf.f i) = snf.a i * snf.bN.repr ⟨_, hmem k⟩ i := h2
      rw [h3]
      intro hu
      exact h ⟨i, rfl, isUnit_of_mul_isUnit_left hu⟩
    · have h0 := snf.repr_eq_zero_of_notMem_range ⟨_, hmem k⟩ hj
      have h0' : snf.bM.repr (fun i => P i k) j = 0 := h0
      rw [h0']
      exact not_isUnit_zero

end GlobalTheory.SmithOE

namespace GlobalTheory.SmithOE

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsDiscreteValuationRing ↥bk.OE → ∀ (d' : ℕ) (P : Matrix (Fin d') (Fin d') (WCb l)), (∀ i j, P i j ∈ bk.OE) → ∃ U Uinv : Matrix (Fin d') (Fin d') (WCb l), (∀ i j, U i j ∈ bk.OE) ∧ (∀ i j, Uinv i j ∈ bk.OE) ∧ Uinv * U = 1 ∧ U * Uinv = 1 ∧ ∀ j, (∃ w : Fin d' → WCb l, (fun i => U i j) = P *ᵥ w) ∨ (∀ k, (l : WCb l) ∣ (Uinv * P) j k) := by
  intro l _ K bk _ d' P hP
  have hfac := (GlobalTheory.OEDvr.main l K bk).2.2.2.1
  let P' : Matrix (Fin d') (Fin d') ↥bk.OE := Matrix.of fun i j => ⟨P i j, hP i j⟩
  obtain ⟨U', W', hWU, hUW, hdich⟩ := pid_dichotomy d' P'
  have hP'map : P'.map bk.OE.subtype = P := by ext; rfl
  refine ⟨U'.map bk.OE.subtype, W'.map bk.OE.subtype, fun i j => (U' i j).2, fun i j => (W' i j).2,
    ?_, ?_, fun j => ?_⟩
  · rw [← Matrix.map_mul, hWU, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hUW, Matrix.map_one _ (map_zero _) (map_one _)]
  · rcases hdich j with ⟨w, hw⟩ | hnu
    · left
      refine ⟨fun i => (w i : WCb l), ?_⟩
      rw [← hP'map]
      funext i
      have := congrArg Subtype.val (congrFun hw i)
      rw [Matrix.mulVec, dotProduct] at this ⊢
      simpa using this
    · right
      intro k
      have heq : ((W'.map bk.OE.subtype) * P) j k = (((W' * P') j k : ↥bk.OE) : WCb l) := by
        rw [← hP'map, ← Matrix.map_mul]; rfl
      rw [heq]
      have hk := hnu k
      generalize (W' * P') j k = x at hk ⊢
      by_cases hx : (x : WCb l) = 0
      · rw [hx]; exact dvd_zero _
      obtain ⟨m, v, v', hv, hv', hvv, hxe⟩ := hfac x x.2 hx
      cases m with
      | zero =>
        exfalso
        apply hk
        refine isUnit_iff_exists_inv.2 ⟨⟨v', hv'⟩, Subtype.ext ?_⟩
        change (x : WCb l) * v' = 1
        rw [hxe, pow_zero, one_mul, hvv]
      | succ m =>
        exact ⟨(l : WCb l) ^ m * v, by rw [hxe, pow_succ]; ring⟩

end GlobalTheory.SmithOE
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem compV_mem_unipB (v : HeightOneSpectrum (𝓞 E)) {u : GA E n} (hu : u ∈ NA E n) :
    compV E n v u ∈ GlobalTheory.SmGL.unipB (v.adicCompletion E) (Fin n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp [compV, h1 i j hij]
  · simp [compV, h2 i]

theorem compV_tl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (v : HeightOneSpectrum (𝓞 E)) :
    compV E n v (tl n ϖ l) = GlobalTheory.IwaCell.tD (ϖ v) (l v) := by
  rw [tl_eq_diagT]
  apply Units.ext
  rw [GlobalTheory.IwaCell.val_tD]
  ext i j
  simp [compV, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    have hc : ∀ x : Af E, pFin E (GlobalTheory.CuspRep.corner (sFin E) x) = x := fun x => by
      show ((1 : InfiniteAdeleRing E × Af E) - ((0 : InfiniteAdeleRing E), (1 : Af E)) + ((0 : InfiniteAdeleRing E), x)).2 = x
      simp
    have hf : ∀ y : (Af E)ˣ, ((finId E y : Ad E)) = GlobalTheory.CuspRep.corner (sFin E) (y : Af E) := fun y => rfl
    rw [hf, hc]
    congr 1
    show ((ϖ v ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = _
    rw [Finsupp.mapRange_apply, Units.val_zpow_eq_zpow_val]
  · simp

end GlobalTheory.CellDec

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem ord_of_isUnifV {v : HeightOneSpectrum (𝓞 E)} {x : (v.adicCompletion E)ˣ}
    (hx : IsUnifV E v (x : v.adicCompletion E)) : GlobalTheory.SmGL.ord (v.adicCompletion E) x = 1 := by
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, hx]
  rfl

theorem compV_mem_cell (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) {S : Finset (HeightOneSpectrum (𝓞 E))}
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {g : GA E n} (h : (tl n ϖ l)⁻¹ * g ∈ C0 E n S)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∉ S) : compV E n v g ∈ GlobalTheory.IwaCell.cell (ϖ v) (l v) := by
  obtain ⟨u, hu, k, hk, e⟩ := h
  have hg : g = tl n ϖ l * u * (tl n ϖ l)⁻¹ * tl n ϖ l * k := by
    rw [inv_mul_eq_iff_eq_mul] at e
    rw [e]; group
  have hkv : compV E n v k ∈ GlobalTheory.SplitWeil.KO (v.adicCompletion E) (Fin n) := by
    rw [GlobalTheory.HeckeEigConj.KO_eq_KGL]
    have := (Subgroup.mem_iInf.1 hk) v
    exact Subgroup.mem_comap.1 ((Subgroup.mem_iInf.1 this) hv)
  refine ⟨compV E n v (tl n ϖ l * u * (tl n ϖ l)⁻¹), compV_mem_unipB v (tl_conj_mem ϖ l hu), compV E n v k, hkv, ?_⟩
  rw [hg, map_mul, map_mul, compV_tl]

end GlobalTheory.CellDec

theorem GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) →
    ∀ (l l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n), (∀ v ∈ S, l v = 0) → (∀ v ∈ S, l' v = 0) →
      (GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → (GlobalTheory.CellDec.tl n ϖ l')⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → l = l' := by
  intro E _ _ n S ϖ hϖ l l' g hl hl' h h'
  ext v : 1
  by_cases hv : v ∈ S
  · rw [hl v hv, hl' v hv]
  · exact GlobalTheory.IwaCell.eq_of_mem_cell (GlobalTheory.CellDec.ord_of_isUnifV (hϖ v))
      (GlobalTheory.CellDec.compV_mem_cell ϖ l h hv) (GlobalTheory.CellDec.compV_mem_cell ϖ l' h' hv)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.rallisIntegrand_factorises_on_levelCoset : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T), LevFix R i t → FactInf R i t → RealLow R i t → LevProd R i → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v, IsUnitVec R i v → ∀ (w : (R.cV i).W) (x y : (R.HW i (sg0 D A)).H), (∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), dimProd A i * ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * (u * γ)) ∂(R.νW i) = trPair R i γ x y * ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u) ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ) → ∀ γ ∈ GfC (Wc D i), ∀ h ∈ realLev R i, dimProd A i * rallisF R i t μ 𝓕 v (jointVec R i t v w) x y (γ * h) = thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) * coef R i t μ 𝓕 γ * trPair R i γ x y * (lowCoefSq R i v h : ℂ) := by
  first | exact @GlobalTheory.RawLift.Pointwise.rallisF_point | exact GlobalTheory.RawLift.Pointwise.rallisF_point | (intros; apply GlobalTheory.RawLift.Pointwise.rallisF_point <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

theorem _root_.GlobalTheory.T.galois_periodRatio_mem_unramified_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ g : ↥(GK K), ∃ a : ↥(K0 K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B a * x := by
  first | exact @GlobalTheory.PeriodQuot.galois_periodRatio_mem_unramified | exact GlobalTheory.PeriodQuot.galois_periodRatio_mem_unramified | (intros; apply GlobalTheory.PeriodQuot.galois_periodRatio_mem_unramified <;> assumption)
end
