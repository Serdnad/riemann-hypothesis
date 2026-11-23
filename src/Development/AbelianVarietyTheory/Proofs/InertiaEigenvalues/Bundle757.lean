module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle609
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle721
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle749
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle736
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle750
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle745
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle744
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle572
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle558
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle621
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle682
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle751
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealisesEtaleFCrystalPullbackGalois
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtale
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle028
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle082
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle536
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle746
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal



theorem GlobalTheory.BKLim.limvec_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, R n i j ∈ bk.OE) → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v) := by
  intro l _ K bk τ hτ d N ρ tw F T0 R hR hF v hv
  have hcl := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  have hevW : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  have key : ∀ (k : ℕ) (z : WCb l), (l : WCb l) ^ k ∣ z ↔
      Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ k}) z = 0 := fun k z => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨fun i => ?_, ?_⟩
  · apply hcl.2.1
    intro n
    obtain ⟨s', hs'⟩ := hv n
    refine ⟨(R n *ᵥ fun j => bk.evW (s' j)) i, ?_, hs' i⟩
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hR n i j) (hevW _)
  · have hinc : ∀ x : ℤ_[l], inclW l (algebraMap ℤ_[l] (Ainf l) x) = algebraMap ℤ_[l] (WCb l) x :=
      fun x => (inclWA l).commutes x
    have hx : ∀ i k, ∃ a : Ainf l, (l : WCb l) ^ k ∣
        (l : WCb l) ^ 0 * (inclW l τ ^ N • (T0 *ᵥ v)) i - inclW l (1 * a) := by
      intro i k
      obtain ⟨s', hs'⟩ := hv k
      obtain ⟨Y, Y', hY, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N (tw.d' k) (fun g => (tw.ρ' k g).val) (F k)
      refine ⟨(((tw.Pi k).map (algebraMap ℤ_[l] (Ainf l)) * Y) *ᵥ fun j => bk.ev (s' j)) i, ?_⟩
      set q := Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ k}) with hq
      rw [key, pow_zero, one_mul, one_mul, map_sub, sub_eq_zero]
      have h1 : (fun i => q (v i)) = fun i => q ((R k *ᵥ fun j => bk.evW (s' j)) i) := funext fun i => by
        have := (key k _).1 (hs' i); rwa [Pi.sub_apply, map_sub, sub_eq_zero] at this
      have h2 : (zW (tw.Pi k) * (F k).T).map q = (T0 * R k).map q := by
        ext i j; have := (key k _).1 (hF k i j); rwa [Matrix.sub_apply, map_sub, sub_eq_zero] at this
      have e1 : inclW l ((((tw.Pi k).map (algebraMap ℤ_[l] (Ainf l)) * Y) *ᵥ fun j => bk.ev (s' j)) i) =
          (inclW l τ ^ N • ((zW (tw.Pi k) * (F k).T) *ᵥ fun j => bk.evW (s' j))) i := by
        rw [RingHom.map_mulVec, Matrix.map_mul, hY, Matrix.map_map]
        have : (tw.Pi k).map ((inclW l) ∘ (algebraMap ℤ_[l] (Ainf l))) = zW (tw.Pi k) := by
          ext a b; simp [zW, hinc]
        rw [this, Matrix.mul_smul, Matrix.smul_mulVec]
        rfl
      rw [e1, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
        RingHom.map_mulVec, RingHom.map_mulVec, h2, Matrix.map_mul, ← Matrix.mulVec_mulVec]
      have h1' : (⇑q ∘ v) = (R k).map q *ᵥ (⇑q ∘ fun j => bk.evW (s' j)) := funext fun j => by
        rw [Function.comp_apply, ← RingHom.map_mulVec]; exact congrFun h1 j
      rw [h1']
    refine ⟨fun i => Classical.choose (GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) 0 _ (hx i)), funext fun i => ?_⟩
    have := Classical.choose_spec (GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) 0 _ (hx i))
    rw [one_mul] at this
    exact this.symm
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem breuilKisinDatumRadius_pos_and_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have h1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := by
    have := bk.deg_pos
    positivity
  refine ⟨NNReal.rpow_pos (by exact_mod_cast hl.out.pos), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg h1 (neg_neg_of_pos he)

theorem wseed_Z_isUnit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ)
    (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (k : ℕ)
    (S' : Matrix (Fin d) (Fin d) (Ainf l)),
    Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) →
    (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z.map j = Y.map bk.iA) → IsUnit Z := by
  intro l _ K bk τ hτ d ρ _ s Y Z k S' hYS hW
  obtain ⟨hρ0, hρ1⟩ := breuilKisinDatumRadius_pos_and_lt_one bk
  have hu : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  let j0 : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map (u := (X : bk.S)) (ρ := bk.ρ₀) bk.ev hu
  have hj0 : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j0 := isDiscMap_map bk.ev hu
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨cD, hcD1, hcD2, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j0 hj0
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB (2 * s.N * d)

  set δ := Z.det with hδ
  have hdet : j0 δ * (s.W.det * bk.iA S'.det) =
      bk.iA (bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d)) := by
    have h1 := congrArg (fun M => bk.iA M.det) hYS
    simp only [det_mul, det_smul, det_one, mul_one, Fintype.card_fin] at h1
    have h2 : bk.iA Y.det = s.W.det * j0 δ := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hW j0 hj0, det_mul, hδ, RingHom.map_det,
        RingHom.mapMatrix_apply]
    rw [map_mul, h2] at h1
    have e : bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d) = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) ^ d := by
      rw [map_pow, map_natCast]; ring
    rw [e, ← h1]
    ring
  have hdvd : ∀ i, δ ∣ toDisc l (X : bk.S) bk.ρ₀ (TB.c i (τ ^ (2 * s.N * d))) := by
    intro i
    have h3 := congrArg (cD i) hdet
    rw [hcD2, hcD1, TB.c_mul, map_mul (toDisc l (X : bk.S) bk.ρ₀)] at h3
    have hunit : IsUnit (toDisc l (X : bk.S) bk.ρ₀ ((l : bk.S) ^ (k * d))) := by
      rw [map_pow, map_natCast]; exact (isUnit_l_disc l _ _).pow _
    exact (hunit.dvd_mul_left).1 ⟨_, h3.symm⟩
  have hle : Ideal.span (Set.range fun i => TB.c i (τ ^ (2 * s.N * d))) ≤
      (Ideal.span {δ}).comap (toDisc l (X : bk.S) bk.ρ₀) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_span_singleton.2 (hdvd i)
  have hl := Ideal.mem_span_singleton.1 (hle hr)
  rw [map_pow, map_natCast] at hl
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_dvd_unit hl ((isUnit_l_disc l _ _).pow _)

end GlobalTheory.BKLim
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem GlobalTheory.BKLim.wseed_frob_inverse : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS * s.W'.map Φ = (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) * bk.iS bk.E ^ (2 * s.N)) • s.W' := by
  intro l _ K bk τ hτ d ρ hρ s Φ hΦ
  obtain ⟨h0, h1⟩ := GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.radius_mem l K bk
  haveI := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1
  have hτ0 := (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).2.1
  refine GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.frob_inverse Φ s.W s.W' _ (bk.iA τ ^ (2 * s.N)) _ _ (pow_ne_zero _ hτ0) s.W_mul
    (GlobalTheory.T.frobenius_matrix_relation_discrete l K bk τ hτ d ρ hρ s Φ hΦ) ?_
  have h2 : Φ (bk.iA τ) = bk.iS bk.E * bk.iA τ := by
    have h3 := hΦ.ext τ
    rw [hτ.1, map_mul] at h3
    exact h3
  rw [map_pow, h2, mul_pow]
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isStablePrismHom_of_localizationAway : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (s : B.A) (h : Hom B C), (∃ t ∈ B.I, ∀ x ∈ B.I, ∃ k : ℕ, s ^ k * x ∈ Ideal.span {t}) → IsLoc s h → Stable h := by
  first | exact @GlobalTheory.BSP.stable_of_isLoc | exact GlobalTheory.BSP.stable_of_isLoc | (intros; apply GlobalTheory.BSP.stable_of_isLoc <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_beta_next_coeff_theta_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (g : ↥(GK K)) (w : Ainf l), Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w → ∀ (m k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → ∀ (i n : ℕ), i + 1 ≤ m → ∀ γ : Matrix (Fin d) (Fin d) bk.S, (∀ p q, bk.E ^ i ∣ (β - (l : bk.S) ^ n • γ) p q) → ∃ δ : Matrix (Fin d) (Fin d) bk.S, (∀ p q, bk.E ^ (i + 1) ∣ (β - (l : bk.S) ^ n • γ - bk.E ^ i • δ) p q) ∧ ∀ p q, ∃ y : OC l, Per.θ l (bk.ev (δ p q)) * (Per.θ l w ^ i - 1) = (l : OC l) ^ n * y := by
  first | (exact @GlobalTheory.BKLim.beta_step) | (exact GlobalTheory.BKLim.beta_step) | (intros; apply GlobalTheory.BKLim.beta_step  <;> assumption)
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.CoverDesc

def solSub {l : ℕ} {R : Type} [CommRing R] {d : ℕ} {B C D : Obj l R} (h : Hom B C) (p q : Hom C D)
    (hpq : p.comp h = q.comp h) (E : Matrix (Fin d) (Fin d) D.A) :
    letI := h.f.toAlgebra; Submodule B.A (Fin d → C.A) :=
  letI := h.f.toAlgebra
  { carrier := {z | (fun i => p.f (z i)) = E.mulVec fun i => q.f (z i)}
    add_mem' := by
      intro a b ha hb
      change (fun i => p.f (a i + b i)) = E.mulVec fun i => q.f (a i + b i)
      have e1 : (fun i => p.f (a i + b i)) = (fun i => p.f (a i)) + fun i => p.f (b i) := by
        funext i; exact map_add _ _ _
      have e2 : (fun i => q.f (a i + b i)) = (fun i => q.f (a i)) + fun i => q.f (b i) := by
        funext i; exact map_add _ _ _
      rw [e1, e2, Matrix.mulVec_add]
      exact congrArg₂ (· + ·) ha hb
    zero_mem' := by
      change (fun i => p.f 0) = E.mulVec fun i => q.f 0
      simp only [map_zero]
      exact (Matrix.mulVec_zero _).symm
    smul_mem' := by
      intro b z hz
      change (fun i => p.f (h.f b * z i)) = E.mulVec fun i => q.f (h.f b * z i)
      have hc : p.f (h.f b) = q.f (h.f b) := congrArg (fun k : Hom B D => k.f b) hpq
      have e1 : (fun i => p.f (h.f b * z i)) = p.f (h.f b) • fun i => p.f (z i) := by
        funext i; exact map_mul _ _ _
      have e2 : (fun i => q.f (h.f b * z i)) = p.f (h.f b) • fun i => q.f (z i) := by
        funext i; rw [map_mul, ← hc]; rfl
      rw [e1, e2, Matrix.mulVec_smul]
      exact congrArg _ hz }

theorem lift_mod {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d) {B C D : Obj l ↥(OL K)}
    (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D) (hc : Cover h) (hpo : IsPO h h p q)
    (v : Fin d → C.A ⧸ adI C ^ 1)
    (hv : (fun i => qmap p 1 (v i)) =
      ((S.ε (p.comp f) (q.comp f)).map (Ideal.Quotient.mk (adI D ^ 1))).mulVec fun i => qmap q 1 (v i)) :
    ∃ z : Fin d → C.A, (fun i => p.f (z i)) = (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) ∧
      ∀ i, Ideal.Quotient.mk (adI C ^ 1) (z i) = v i := by
  choose z₀ hz₀ using fun i => Ideal.Quotient.mk_surjective (I := adI C ^ 1) (v i)
  obtain rfl : (fun i => Ideal.Quotient.mk (adI C ^ 1) (z₀ i)) = v := funext hz₀
  have hyp : ∀ i, p.f (z₀ i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z₀ j)) i ∈ adI D ^ 1 := by
    intro i
    rw [← Ideal.Quotient.eq]
    have e := congrFun hv i
    simp only [qmap_mk] at e
    exact e.trans (RingHom.map_mulVec _ _ _ i).symm
  have H := GlobalTheory.T.exists_descent_solution_lift_mod_prism_ideal l K bk d S B C D h f p q hc hpo z₀ hyp
  exact ⟨H.choose, H.choose_spec.2, fun i => Ideal.Quotient.eq.2 (H.choose_spec.1 i)⟩



theorem exists_descent : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C), Cover h → ∃ (P : Type) (_ : AddCommGroup P) (_ : Module B.A P) (_ : Module.Finite B.A P) (_ : Module.Projective B.A P) (u : P →ₛₗ[h.f] (Fin d → C.A)), SemiBC u ∧ ∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → ∀ x, (fun i => p.f (u x i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (u x i) := by
  intro l _ K bk d S B C h f hc
  obtain ⟨D, p₀, q₀, hpo⟩ := hc.stable.po C h
  have hcomm : ∀ b, p₀.f (h.f b) = q₀.f (h.f b) := fun b => congrArg (fun k : Hom B D => k.f b) hpo.comm
  letI : Algebra (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := (qmap h 1).toAlgebra
  obtain ⟨N₁, hN₁, hfin, hproj, hbc⟩ := GlobalTheory.T.stratifiedPhiModule_descent_finite_level l K bk d S B C D h f p₀ q₀ hc hpo 1
  haveI hcB : IsAdicComplete (adI B ^ 1) B.A := by rw [pow_one]; exact B.complete
  obtain ⟨P, _, _, _, _, u₁, hu₁⟩ := GlobalTheory.T.exists_finite_projective_lift_of_isAdicComplete B.A (adI B ^ 1) ↥N₁
  letI : Algebra B.A C.A := h.f.toAlgebra
  haveI : IsScalarTower B.A (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := IsScalarTower.of_algebraMap_eq (fun b => rfl)
  have hs : ∀ (b : B.A) (y : ↥N₁), (Ideal.Quotient.mk (adI B ^ 1) b) • y = b • y := fun b y => Subtype.ext rfl
  let u₁' : P →ₗ[B.A] ↥N₁ := { toFun := fun x => u₁ x, map_add' := fun x y => u₁.map_add x y, map_smul' := fun b x => (u₁.map_smulₛₗ b x).trans (hs b (u₁ x)) }
  have hb1 : IsBaseChange (B.A ⧸ adI B ^ 1) u₁' := (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange B.A (B.A ⧸ adI B ^ 1) P ↥N₁ u₁ u₁' (fun x => rfl)).1 hu₁
  have hb2 := hb1.comp hbc
  let M := solSub h p₀ q₀ hpo.comm (S.ε (p₀.comp f) (q₀.comp f))
  have memM : ∀ z, z ∈ M ↔ (fun i => p₀.f (z i)) = (S.ε (p₀.comp f) (q₀.comp f)).mulVec fun i => q₀.f (z i) := fun z => Iff.rfl
  have memN : ∀ z : Fin d → C.A, z ∈ M → (fun i => Ideal.Quotient.mk (adI C ^ 1) (z i)) ∈ N₁ := by
    intro z hz
    rw [hN₁]
    funext i
    simp only [qmap_mk]
    have e : p₀.f (z i) = (S.ε (p₀.comp f) (q₀.comp f)).mulVec (fun j => q₀.f (z j)) i := congrFun ((memM z).1 hz) i
    exact (congrArg (Ideal.Quotient.mk (adI D ^ 1)) e).trans (RingHom.map_mulVec _ _ _ i)
  let π : M →ₗ[B.A] ↥N₁ :=
    { toFun := fun z => ⟨fun i => Ideal.Quotient.mk (adI C ^ 1) (z.1 i), memN z.1 z.2⟩
      map_add' := fun a b => Subtype.ext (funext fun i => map_add _ _ _)
      map_smul' := fun b z => Subtype.ext (funext fun i => map_mul _ _ _) }
  have hπ : Function.Surjective π := by
    intro n
    have H := lift_mod S h f p₀ q₀ hc hpo n.1 ((hN₁ n.1).1 n.2)
    exact ⟨⟨H.choose, (memM _).2 H.choose_spec.1⟩, Subtype.ext (funext H.choose_spec.2)⟩
  have HG := Module.projective_lifting_property π u₁' hπ
  let g := HG.choose
  have hg : π ∘ₗ g = u₁' := HG.choose_spec
  let u' : P →ₗ[B.A] (Fin d → C.A) := M.subtype ∘ₗ g
  let u : P →ₛₗ[h.f] (Fin d → C.A) :=
    { toFun := fun x => u' x, map_add' := fun x y => u'.map_add x y, map_smul' := fun b x => u'.map_smul b x }
  have huM : ∀ x, u x ∈ M := fun x => (g x).2
  refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, u, ?_, ?_⟩
  · haveI := C.complete
    have hV : IsBaseChange C.A u' := by
      have hgq := (IsBaseChange.linearMap C.A (C.A ⧸ adI C ^ 1)).finitePow (Fin d)
      refine GlobalTheory.T.isBaseChange_of_isBaseChange_quotient_comp B.A C.A (adI C ^ 1) ?_ P (Fin d → C.A) _ u' _ hgq ?_
      · exact le_trans (Ideal.pow_le_self one_ne_zero) (IsAdicComplete.le_jacobson_bot _)
      · have heq : ((Algebra.linearMap C.A (C.A ⧸ adI C ^ 1)).compLeft (Fin d)).restrictScalars B.A ∘ₗ u' =
            (N₁.subtype.restrictScalars B.A).comp u₁' := by
          refine LinearMap.ext fun x => funext fun i => ?_
          exact congrArg (fun y : ↥N₁ => y.1 i) (LinearMap.congr_fun hg x)
        rw [heq]; exact hb2
    exact (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange B.A C.A P (Fin d → C.A) u u' (fun x => rfl)).2 hV
  · intro Q p q hpq x
    have HC := GlobalTheory.T.prismPushoutModAdicPow_universal l _ B C C D h h p₀ q₀ hpo Q p q hpq
    obtain ⟨c, ⟨hcp, hcq⟩, -⟩ := HC
    subst hcp hcq
    have hx := (memM _).1 (huM x)
    rw [show (c.comp p₀).comp f = c.comp (p₀.comp f) from rfl, show (c.comp q₀).comp f = c.comp (q₀.comp f) from rfl,
      ← S.ε_nat c]
    funext i
    change c.f (p₀.f (u x i)) = _
    have e : p₀.f (u x i) = (S.ε (p₀.comp f) (q₀.comp f)).mulVec (fun j => q₀.f (u x j)) i := congrFun hx i
    rw [e, RingHom.map_mulVec]
    rfl

end GlobalTheory.BSP.CoverDesc
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.FrobTwistKappa

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (g : ↥(GK K)) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (V : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (ε : Matrix (Fin d) (Fin d) (Ainf l)), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Ψ → s.κ g * s.F.map (bk.iS.comp C) = s.F.map (bk.iS.comp C) * (s.κ g).map Φ → G (bk.iS bk.E) ^ s.N • (V.map i * ε.map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (V.map i).map G) → G (bk.iS (frobS l bk.a bk.E)) ^ s.N • ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i * (ε.map WittVector.frobenius).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ s.N • (s.κ g * ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i).map G) := by
  intro l _ K bk τ d ρ s g G Φ i Ψ V ε hG hΦ hi hΨ hκ h
  have hsmul : ∀ (f : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (c : bk.DA bk.ρ₀) (M : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)),
      (c • M).map f = f c • M.map f := fun f c M => by ext a b; simp
  have hΦG : ∀ x, Φ (G x) = G (Φ x) := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp (Per.σA (g : GQ l)) =
        (Per.σA (g : GQ l)).comp WittVector.frobenius :=
      RingHom.ext fun a => (GlobalTheory.Prism.PullGal.σA_frobenius (g : GQ l) a).symm
    have hc := (GlobalTheory.BSP.FrobRational.isDiscMap_comp hG hΦ).unique
      (e ▸ GlobalTheory.BSP.FrobRational.isDiscMap_comp hΦ hG)
    exact fun x => RingHom.congr_fun hc x
  have hΦi : Φ.comp i = i.comp Ψ := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev = bk.ev.comp (frobS l bk.a) :=
      RingHom.ext fun x => (bk.ev_frob x).symm
    exact (GlobalTheory.BSP.FrobRational.isDiscMap_comp hi hΦ).unique (e ▸ GlobalTheory.BSP.FrobRational.isDiscMap_comp hΨ hi)
  have hΦiS : ∀ x, Φ (bk.iS x) = bk.iS (frobS l bk.a x) := fun x => by
    change Φ (toDisc l (bk.ev X) bk.ρ₀ (bk.ev x)) = toDisc l (bk.ev X) bk.ρ₀ (bk.ev (frobS l bk.a x))
    rw [hΦ.ext, bk.ev_frob]
  have hFD : (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C)).map i = s.F.map (bk.iS.comp C) := by
    ext a b
    exact hi.ext _
  have hGFD : (s.F.map (bk.iS.comp C)).map G = s.F.map (bk.iS.comp C) := by
    ext a b
    change G (toDisc l (bk.ev X) bk.ρ₀ (bk.ev (C (s.F a b)))) = toDisc l (bk.ev X) bk.ρ₀ (bk.ev (C (s.F a b)))
    rw [hG.ext, bk.ev_C, bk.gal_w]
  have e1 : (V.map i).map Φ = (V.map Ψ).map i := by
    ext a b
    exact RingHom.congr_fun hΦi (V a b)
  have e2 : (ε.map bk.iA).map Φ = (ε.map WittVector.frobenius).map bk.iA := by
    ext a b
    exact hΦ.ext _
  have e3 : ((V.map i).map G).map Φ = ((V.map Ψ).map i).map G := by
    ext a b
    simp only [Matrix.map_apply]
    rw [hΦG]
    exact congrArg G (RingHom.congr_fun hΦi (V a b))
  have h1 := congrArg (fun M => M.map Φ) h
  simp only [hsmul, Matrix.map_mul] at h1
  rw [map_pow, map_pow, hΦG, hΦiS, e1, e2, e3] at h1
  have eL : (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i =
      s.F.map (bk.iS.comp C) * (V.map Ψ).map i := by
    rw [Matrix.map_mul, hFD]
  rw [eL, Matrix.map_mul, hGFD, Matrix.mul_assoc (s.F.map (bk.iS.comp C)), ← Matrix.mul_assoc (s.κ g), hκ,
    Matrix.mul_assoc]
  have h2 := congrArg (fun M => s.F.map (bk.iS.comp C) * M) h1
  simp only [Matrix.mul_smul] at h2
  exact h2

end GlobalTheory.BKLim.FrobTwistKappa
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.limit_breuilKisin_basis_invariant_etale : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)), IsUnit T0 → (∀ n, ∃ (R : Matrix (Fin d) (Fin (tw.d' n)) (WCb l)) (R' : Matrix (Fin (tw.d' n)) (Fin d) (WCb l)), (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (R * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j)) → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g).val * T0.map (galW l (g : GQ l)) = T0) ∧ ∃ A0 A0' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A0 i j ∈ bk.OE) ∧ (∀ i j, A0' i j ∈ bk.OE) ∧ T0.map (frobW l) = T0 * A0 ∧ A0 * A0' = 1 := by
  first | exact @GlobalTheory.LimBasis.main | exact GlobalTheory.LimBasis.main | (intros; apply GlobalTheory.LimBasis.main; all_goals assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section
namespace GlobalTheory.LagMeans



theorem lagTerm_eq_of_means : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), IsLagFrame W Y C → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ f₁ f₁' f₂ : WO V W → ℂ, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₁' → IsThetaFunO ψ V W f₂ → (∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, f₁ (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f₁' (HMul.hMul (I.map (incA D)) y + x) ∂ν) → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C f₁' f₂ := by
  intro D ψ hψ V W μ 𝓕 hμ Y C hC s I hI hspan ν 𝓨 hν f₁ f₁' f₂ h₁ h₁' h₂ hmean
  have hmem : ∀ j, ((fun a => I a j), (0 : Fin W.rank → D.host.E)) ∈ Y.1 := fun j => by
    have : (fun a => I a j) ∈ Y.1.comap (LinearMap.inl D.host.E _ _) := hspan ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  have mcol : ∀ k, ((fun a => C.1 a k), (fun a => C.2 a k)) ∈ Y.1 := fun k => hC ▸ Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨t, J, K, L, M, e1, e2, e3, e4, e5, e6, e7⟩ := GlobalTheory.T.exists_adapted_frame_of_isotropic_columns' D.host.E W.rank Y.1 Y.2.1 C hC s I hI.2.1 hmem
  obtain ⟨η, 𝓥, hη⟩ := GlobalTheory.MixModel.exists_isCovolOne D t V.rank
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.integral_fundamentalDomain_eq_iterated_rationalSplitting D W.rank V.rank s t J K L M e3 e4 e5 e6 e7 μ 𝓕 hμ ν 𝓨 hν η 𝓥 hη
  have hB : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram * C.1 = 0 := by
    rw [Matrix.mul_assoc]
    funext j k
    have := Y.2.2 _ (hmem j) _ (mcol k)
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero] at this
    simpa only [Matrix.mul_apply, GlobalTheory.MixModel.cT_sig, Matrix.conjTranspose_apply, Matrix.zero_apply] using this
  have hψ' : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have per : ∀ f, IsThetaFunO ψ V W f → ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank V.rank, ∀ u : Mx D W.rank V.rank,
      f (ratMul C.1 (γ + u)) * star (f₂ (ratMul C.2 (γ + u))) = f (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) := by
    rintro f hf _ ⟨γ, rfl⟩ u
    exact GlobalTheory.RawLift.Model.integrand_periodic hψ' hC hf h₂ γ u
  have cont : ∀ f, IsThetaFunO ψ V W f → Continuous fun u : Mx D W.rank V.rank => f (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) :=
    fun f hf => (hf.cont.comp (continuous_const.matrix_mul continuous_id)).mul
      (continuous_star.comp (h₂.cont.comp (continuous_const.matrix_mul continuous_id)))
  unfold lagTerm
  rw [hκ _ (cont f₁ h₁) (per f₁ h₁), hκ _ (cont f₁' h₁') (per f₁' h₁')]
  congr 1
  congr 1
  funext v
  have r1 : ∀ y : Mx D s V.rank, ratMul C.1 (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) =
      HMul.hMul (I.map (incA D)) y + HMul.hMul ((C.1 * K).map (incA D)) v := fun y => by
    unfold ratMul
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, e1]
  have r2 : ∀ y : Mx D s V.rank, ratMul C.2 (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) =
      HMul.hMul ((C.2 * K).map (incA D)) v := fun y => by
    unfold ratMul
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, e2,
      Matrix.map_zero (incA D) (map_zero (incA D))]
    simp only [Matrix.zero_mul, zero_add]
  simp only [r1, r2]
  rw [integral_mul_const, integral_mul_const]
  congr 1
  refine hmean _ ?_
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.mul_assoc, hB, Matrix.zero_mul, Matrix.map_zero (incA D) (map_zero (incA D))]
  exact Matrix.zero_mul _

end GlobalTheory.LagMeans
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], (∀ g : GQ l, ∃ h ∈ GK (ϖ.field a), ∃ k ∈ ϖ.GKinf, g = h * k) ∧ (∀ k ∈ ϖ.GKinf, ∃ γ, Covers ↥LL.1 (thetaW a LL) ϖ k γ) ∧ (∀ γ : TameGal ↥LL.1 l e a, ∃ k ∈ ϖ.GKinf, Covers ↥LL.1 (thetaW a LL) ϖ k γ) ∧ (∀ (k : GQ l) (γ γ' : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → Covers ↥LL.1 (thetaW a LL) ϖ k γ' → γ = γ') ∧ (∀ (k k' : GQ l) (γ γ' : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → Covers ↥LL.1 (thetaW a LL) ϖ k' γ' → Covers ↥LL.1 (thetaW a LL) ϖ (k * k') (γ * γ')) ∧ (∀ k : GQ l, Covers ↥LL.1 (thetaW a LL) ϖ k (1 : TameGal ↥LL.1 l e a) ↔ k ∈ ϖ.GfieldInf a) ∧ ∀ (k : GQ l) (ζ : rootsOfUnity e ↥LL.1), Covers ↥LL.1 (thetaW a LL) ϖ k (TameGal.inertia ζ : TameGal ↥LL.1 l e a) → ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), Covers ↥LL.1 (thetaW a LL) ϖ (k' : GQ l) (TameGal.inertia ζ : TameGal ↥LL.1 l e a) ∧ (((ζ : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 = (k' : GQ l) (ϖ.seq 0) := by
  first | exact @GlobalTheory.TameCover.main | exact GlobalTheory.TameCover.main | (intros; apply GlobalTheory.TameCover.main <;> assumption)
end
