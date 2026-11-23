module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle759
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle599
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle687
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle721
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle736
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle761
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle764
import Formalism.PeriodIntegrals.Bundle019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle760
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
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished

@[expose] public section

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.InvLift

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (m : ℕ)

def InvSet : Subring bk.S where
  carrier := {x | ∀ g : ↥(GK K), bk.ev bk.E ^ m ∣ Per.σA (g : GQ l) (bk.ev x) - bk.ev x}
  zero_mem' g := by simp
  one_mem' g := by simp
  neg_mem' {x} hx g := by
    have := (hx g).neg_right
    simpa [map_neg, neg_sub, sub_eq_add_neg, add_comm] using this
  add_mem' {x y} hx hy g := by
    have h := dvd_add (hx g) (hy g)
    rw [map_add (f := _), map_add (f := _)]
    convert h using 1
    ring
  mul_mem' {x y} hx hy g := by
    have h := dvd_add (dvd_mul_of_dvd_right (hy g) (Per.σA (g : GQ l) (bk.ev x)))
      (dvd_mul_of_dvd_left (hx g) (bk.ev y))
    rw [map_mul, map_mul]
    convert h using 1
    ring

theorem C_mem (w : Wq l bk.a) : (C w : bk.S) ∈ InvSet bk m := fun g => by
  rw [bk.ev_C, bk.gal_w, sub_self]
  exact dvd_zero _

omit hl in
theorem coe_sum_fin {R : Type} [CommRing R] {e : ℕ} (c : Fin e → R) :
    ((∑ i, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) : Polynomial R) : R⟦X⟧) = ∑ i, C (c i) * X ^ (i : ℕ) := by

  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  simp [Polynomial.coeToPowerSeries.ringHom_apply]

theorem exists_div (s : bk.S) : ∃ (q : bk.S) (c : Fin bk.Ep.natDegree → Wq l bk.a),
    s = bk.E * q + ∑ i, C (c i) * X ^ (i : ℕ) := by
  haveI : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP
  have hdist : bk.Ep.IsDistinguishedAt (Ideal.span {(l : Wq l bk.a)}) :=
    { mem := fun {i} hi => Ideal.mem_span_singleton.2 (bk.dvd_coeff i hi)
      monic := bk.monic }
  have hI : Ideal.span {(l : Wq l bk.a)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (WittVector.irreducible l (k := Fq l bk.a)).not_isUnit
  obtain ⟨h1, h2⟩ := (hdist.isWeierstrassDivisorAt hI).isWeierstrassDivisionAt_div_mod s
  refine ⟨(hdist.isWeierstrassDivisorAt hI).div s, fun i => ((hdist.isWeierstrassDivisorAt hI).mod s).coeff i,
    h2.trans ?_⟩
  rw [← coe_sum_fin]
  congr 2
  have ho : bk.Ep.natDegree = _ := congr(ENat.toNat $(hdist.coe_natDegree_eq_order_map (bk.Ep : (Wq l bk.a)⟦X⟧) 1
    (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)))
  rw [← ho] at h1
  rw [Polynomial.sum_fin (fun i a => Polynomial.C a * Polynomial.X ^ i) (by simp) h1,
    Polynomial.sum_C_mul_X_pow_eq]

variable {bk m} in
theorem cancel_pow_l (k : ℕ) (a : Ainf l) (h : bk.ev bk.E ^ m ∣ (l : Ainf l) ^ k * a) : bk.ev bk.E ^ m ∣ a := by
  induction k generalizing a with
  | zero => simpa using h
  | succ k ih =>
    apply (GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk m).1
    apply ih
    rwa [pow_succ, mul_assoc] at h

end GlobalTheory.BSP.InvLift


open GlobalTheory.BSP.InvLift in
theorem GlobalTheory.BSP.BK.exists_inv_lift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), ∃ k : ℕ, ∀ s : bk.S, ∃ γ : bk.S, bk.E ∣ γ - (l : bk.S) ^ k * s ∧ ∀ g : ↥(GK K), bk.ev bk.E ^ m ∣ Per.σA (g : GQ l) (bk.ev γ) - bk.ev γ := by
  intro l hl K bk m
  obtain ⟨M, q, hq1, hq2⟩ := GlobalTheory.BSP.BK.exists_approx_root l K bk m
  have hqinv : q ∈ InvSet bk m := fun g => by
    obtain ⟨k, hk⟩ := GlobalTheory.BSP.approx_root_indep l K bk m M q hq1 hq2 (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)
    change bk.ev bk.E ^ m ∣ (l : Ainf l) ^ k * (bk.ev q - Per.σA (g : GQ l) (bk.ev q)) at hk
    rw [← neg_sub]
    exact (cancel_pow_l k _ hk).neg_right
  set e := bk.Ep.natDegree
  refine ⟨M * e, fun s => ?_⟩
  obtain ⟨q', c, hs⟩ := exists_div bk s
  refine ⟨∑ i : Fin e, C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ), ?_, fun g => ?_⟩
  · have key : ∀ i : Fin e, bk.E ∣ C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ) -
        (l : bk.S) ^ (M * e) * (C (c i) * X ^ (i : ℕ)) := by
      intro i
      have h1 : (l : bk.S) ^ (M * e) * X ^ (i : ℕ) = (l : bk.S) ^ (M * (e - i)) * ((l : bk.S) ^ M * X) ^ (i : ℕ) := by
        rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, ← Nat.mul_add]
        congr 3
        have := i.2
        omega
      rw [mul_left_comm, h1]
      have := (hq1.trans (sub_dvd_pow_sub_pow q ((l : bk.S) ^ M * X) i)).mul_left (C (c i) * (l : bk.S) ^ (M * (e - i)))
      convert this using 1
      ring
    have heq : (∑ i : Fin e, C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ)) - (l : bk.S) ^ (M * e) * s =
        (∑ i : Fin e, (C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ) -
          (l : bk.S) ^ (M * e) * (C (c i) * X ^ (i : ℕ)))) - bk.E * ((l : bk.S) ^ (M * e) * q') := by
      rw [hs, Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
      ring
    rw [heq]
    exact dvd_sub (Finset.dvd_sum fun i _ => key i) (dvd_mul_right _ _)
  · have hmem : (∑ i : Fin e, C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ)) ∈ InvSet bk m :=
      Subring.sum_mem _ fun i _ => Subring.mul_mem _ (Subring.mul_mem _ (C_mem bk m _)
        (Subring.pow_mem _ (natCast_mem _ _) _)) (Subring.pow_mem _ hqinv _)
    exact hmem g
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section
namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem seedRec_ρ₀_pos (bk : BK K) : 0 < bk.ρ₀ := by
  unfold BK.ρ₀
  exact NNReal.rpow_pos (by exact_mod_cast hl.out.pos)

theorem seedRec_ρ₀_lt_one (bk : BK K) : bk.ρ₀ < 1 := by
  unfold BK.ρ₀
  apply NNReal.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hl.out.one_lt
  · have : (0:ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
    have : 0 < 1 / (bk.Ep.natDegree : ℝ) := by positivity
    linarith

theorem seedRec_frobS_norm (bk : BK K) :
    ‖toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a X)‖ ≤ bk.ρ₀ := by
  rw [frobS_X]
  refine (norm_toDisc_pow_le (l := l) (u := (X : bk.S)) l (seedRec_ρ₀_pos bk)).trans ?_
  exact pow_le_of_le_one bk.ρ₀.coe_nonneg (by exact_mod_cast (seedRec_ρ₀_lt_one bk).le) hl.out.ne_zero

theorem seedRec_comm (bk : BK K) (j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (hj : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j)
    (Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hΦ : IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ)
    (ΦS : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (hΦS : IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) ΦS) (x : bk.DS bk.ρ₀) :
    Φ (j x) = j (ΦS x) := by
  have h1 : IsDiscMap (l := _) (u := _) (ρ := _) (bk.ev.comp (frobS l bk.a)) (Φ.comp j) :=
    ⟨fun a => by simp [hj.ext, hΦ.ext, bk.ev_frob], fun x => (hΦ.norm_le _).trans (hj.norm_le x)⟩
  have h2 : IsDiscMap (l := _) (u := _) (ρ := _) (bk.ev.comp (frobS l bk.a)) (j.comp ΦS) :=
    ⟨fun a => by simp [hj.ext, hΦS.ext], fun x => (hj.norm_le _).trans (hΦS.norm_le x)⟩
  exact RingHom.congr_fun (h1.unique h2) x

theorem seedRec_frobS_E_ne_zero (bk : BK K) : frobS l bk.a bk.E ≠ 0 := by
  intro h
  have := congrArg (PowerSeries.coeff (l * bk.Ep.natDegree)) h
  simp [frobS, BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree] at this

theorem seedRec_ev_injective (bk : BK K) {ι : Type} (TB : TopBasis bk.ev bk.J ι) : Function.Injective bk.ev := by
  have hb : TB.c TB.i₀ 1 = 1 := by rw [← TB.b_i₀]; exact TB.c_self _
  have hev : ∀ x, TB.c TB.i₀ (bk.ev x) = x := fun x => by simpa [hb] using TB.c_mul TB.i₀ x 1
  intro x y h
  rw [← hev x, h, hev]

theorem seed_coeff_recurrence : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → ∀ (cD : ι → (bk.DA bk.ρ₀ →+ bk.DS bk.ρ₀)), (∀ i a, cD i (bk.iA a) = toDisc l (X : bk.S) bk.ρ₀ (TB.c i a)) → (∀ i x y, cD i (j x * y) = x * cD i y) → (∀ y, HasSum (fun i => j (cD i y) * bk.iA (TB.b i)) y) → (∀ i y, ‖cD i y‖ ≤ ‖y‖) → ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ∀ (i₁ : ι) (a b : Fin d), HasSum (fun i => Φ ((s.W * (s.W'.map (cD i)).map j) a b) * bk.iS (TB.c i₁ (WittVector.frobenius (TB.b i)))) (bk.iS bk.E ^ (2 * s.N) * (s.W * (s.W'.map (cD i₁)).map j) a b) := by
  intro l _ K bk τ hτ d ρ hρ s ι TB j hj cD hc hcm hsum hnorm Φ hΦ i₁ a b
  have h0 := seedRec_ρ₀_pos bk
  have h1 := seedRec_ρ₀_lt_one bk
  obtain ⟨hdom, -, -⟩ := GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1
  let ΦS := Disc.map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := (X : bk.S)) (ρ' := bk.ρ₀)
    (frobS l bk.a) (seedRec_frobS_norm bk)
  have hΦS : IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) ΦS := isDiscMap_map _ _
  have hcomm : ∀ x, Φ (j x) = j (ΦS x) := seedRec_comm bk j hj Φ hΦ ΦS hΦS
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
  have hphi := GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ
  have hwp := GlobalTheory.T.crystallineLattice_frobenius_inverse_matrix l K bk τ hτ d ρ hρ s Φ hΦ
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
    apply seedRec_frobS_E_ne_zero bk
    apply seedRec_ev_injective bk TB
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
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory.SmithQuot

theorem oe_dvr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsDiscreteValuationRing ↥bk.OE := by
  intro l _ K bk
  haveI : PerfectRing (Cb l) l := GlobalTheory.OEDvr.perfectRing_Cb
  obtain ⟨hdivl, -, -, hfac, -⟩ := GlobalTheory.OEDvr.main l K bk
  have hlW : Irreducible ((l : ℕ) : WCb l) := WittVector.irreducible l (k := Cb l)
  have hlO : (l : WCb l) ∈ bk.OE := natCast_mem _ l
  set π : ↥bk.OE := ⟨(l : WCb l), hlO⟩
  have hπ : ¬ IsUnit π := fun h => hlW.not_isUnit (h.map bk.OE.subtype)
  have hfac' : ∀ x : ↥bk.OE, x ≠ 0 → ∃ k : ℕ, Associated (π ^ k) x := by
    intro x hx
    obtain ⟨k, v, v', hv, hv', hvv, hx'⟩ := hfac x x.2 (fun h => hx (Subtype.ext h))
    refine ⟨k, ⟨⟨⟨v, hv⟩, ⟨v', hv'⟩, Subtype.ext hvv, Subtype.ext (by rw [mul_comm]; exact hvv)⟩, ?_⟩⟩
    apply Subtype.ext
    simp [π, hx']
  have hunit : ∀ x : ↥bk.OE, IsUnit (x : WCb l) → IsUnit x := by
    intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    obtain ⟨k, hk⟩ := hfac' x hx0
    rcases k with _ | k
    · exact hk.isUnit_iff.mp (by rw [pow_zero]; exact isUnit_one)
    · exfalso
      obtain ⟨u, hu⟩ := hk
      have : (l : WCb l) ∣ (x : WCb l) := by
        rw [← hu]; exact ⟨(l : WCb l) ^ k * (u : ↥bk.OE), by simp [π, pow_succ]; ring⟩
      exact hlW.not_isUnit (isUnit_of_dvd_unit this hx)
  have hirr : Irreducible π := by
    refine ⟨hπ, ?_⟩
    intro a b hab
    have := hlW.isUnit_or_isUnit (show ((l : ℕ) : WCb l) = (a : WCb l) * (b : WCb l) from congrArg Subtype.val hab)
    exact this.imp (hunit a) (hunit b)
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨π, hirr, fun {x} hx => hfac' x hx⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' n : ℕ) (Q : Matrix (Fin d) (Fin d') (WCb l)) (P : Matrix (Fin d') (Fin d') (WCb l)), 1 ≤ n → (∀ i j, P i j ∈ bk.OE) → (∃ S : Matrix (Fin d') (Fin d) (WCb l), (∀ i j, (l : WCb l) ^ n ∣ (Q * S - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j)) → (∀ v : Fin d' → WCb l, (∀ i, (l : WCb l) ^ n ∣ (Q *ᵥ v) i) ↔ ∃ w, v = P *ᵥ w) → ∃ (Tn : Matrix (Fin d) (Fin d) (WCb l)) (R : Matrix (Fin d) (Fin d') (WCb l)) (R' : Matrix (Fin d') (Fin d) (WCb l)), IsUnit Tn ∧ (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (Q - Tn * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (Q * R' - Tn) i j) := by
  intro l _ K bk d d' n Q P hn hP hS hker
  obtain ⟨S, hS⟩ := hS
  obtain ⟨U, Uinv, hU, hUi, h1, h2, hdich⟩ := GlobalTheory.T.smith_form_coefficientRing_image_or_prime_dvd_row l K bk (oe_dvr l K bk) d' P hP
  classical
  let J : Finset (Fin d') := Finset.univ.filter (fun j => ¬ ∃ w : Fin d' → WCb l, (fun i => U i j) = P *ᵥ w)
  have hi : ∀ j ∉ J, ∀ i, (l : WCb l) ^ n ∣ (Q * U) i j := by
    intro j hj i
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
    have := (hker (fun i => U i j)).mpr hj i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hii : ∀ v : Fin d' → WCb l, (∀ i, (l : WCb l) ^ n ∣ (Q *ᵥ v) i) → ∀ j ∈ J, (l : WCb l) ∣ (Uinv *ᵥ v) j := by
    intro v hv j hj
    obtain ⟨w, rfl⟩ := (hker v).mp hv
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hr := (hdich j).resolve_left hj
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.dvd_sum (fun k _ => (hr k).mul_right _)
  obtain ⟨e, hunit, hdiv⟩ := GlobalTheory.T.wittCompletedTilt_columns_of_right_inverse_mod_pow l d d' n Q S U Uinv J hn hS h1 h2 hi hii
  refine ⟨Q * U.submatrix id (fun k => (e k : Fin d')), Uinv.submatrix (fun k => (e k : Fin d')) id,
    U.submatrix id (fun k => (e k : Fin d')), hunit, fun i j => hUi _ _, fun i j => hU _ _, hdiv, ?_⟩
  intro i j
  simp [Matrix.mul_submatrix_one, Matrix.submatrix]

end GlobalTheory.SmithQuot
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal



namespace GlobalTheory.BKLim.SatLat

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (T0 V V' : Matrix (Fin d) (Fin d) (WCb l)) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit T0 → (∀ i j, V i j ∈ bk.OE) → (∀ i j, V' i j ∈ bk.OE) → V * V' = 1 → Y1.map (inclW l) = inclW l τ ^ N • (T0 * V) → ∃ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Wm Wm' : Matrix (Fin d) (Fin d) (WCb l)), IsUnit (Y.map (inclW l)) ∧ (∀ i j, Wm i j ∈ bk.OE) ∧ (∀ i j, Wm' i j ∈ bk.OE) ∧ Wm * Wm' = 1 ∧ Y.map (inclW l) = inclW l τ ^ N • (T0 * Wm) ∧ ∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a) := by
  intro l _ K bk τ hτ d N T0 V V' Y1 hT0 hV hV' hVV' hY1
  classical
  obtain ⟨htu, -, -, -⟩ := GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ
  have hOEcl := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) (WCb l), M = inclW l τ ^ N • T0 := ⟨_, rfl⟩
  have hMu : IsUnit M.det := by
    rw [hM, Matrix.det_smul]
    exact ((htu.pow N).pow _).mul ((Matrix.isUnit_iff_isUnit_det T0).1 hT0)
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMu
  have hMM' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hMu
  have hVu : IsUnit V.det := by
    have h : V.det * V'.det = 1 := by rw [← Matrix.det_mul, hVV', Matrix.det_one]
    exact ⟨⟨V.det, V'.det, h, by rw [mul_comm]; exact h⟩, rfl⟩
  let ι : (Fin d → Ainf l) → (Fin d → WCb l) := fun y a => inclW l (y a)
  have hιmul : ∀ (A : Matrix (Fin d) (Fin d) (Ainf l)) (v : Fin d → Ainf l),
      ι (A *ᵥ v) = A.map (inclW l) *ᵥ ι v := by
    intro A v; funext i; simp [ι, Matrix.mulVec, dotProduct, map_sum]
  have hevW : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  have hevWι : ∀ c : Fin d → bk.S, ι (fun a => bk.ev (c a)) = fun a => bk.evW (c a) := fun c => rfl
  let mem : (Fin d → Ainf l) → Prop := fun y => ∀ i, (M⁻¹ *ᵥ ι y) i ∈ bk.OE
  have hY1M : Y1.map (inclW l) = M * V := by rw [hY1, hM, Matrix.smul_mul]
  have hmemV : ∀ c : Fin d → bk.S, mem (Y1 *ᵥ fun a => bk.ev (c a)) := by
    intro c i
    show (M⁻¹ *ᵥ ι (Y1 *ᵥ fun a => bk.ev (c a))) i ∈ bk.OE
    rw [hιmul, hevWι, hY1M, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hMM', Matrix.one_mul]
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hV i j) (hevW _)
  obtain ⟨Y, hYu, hYmem⟩ := GlobalTheory.T.ainf_closed_membership_limit l K bk d mem
    (fun i => by
      show (M⁻¹ *ᵥ ι 0) i ∈ bk.OE
      have : ι 0 = 0 := by funext a; simp [ι]
      rw [this, Matrix.mulVec_zero]; exact Subring.zero_mem _)
    (fun y z hy hz i => by
      show (M⁻¹ *ᵥ ι (y + z)) i ∈ bk.OE
      have : ι (y + z) = ι y + ι z := by funext a; simp [ι]
      rw [this, Matrix.mulVec_add]; exact Subring.add_mem _ (hy i) (hz i))
    (fun c y hy i => by
      show (M⁻¹ *ᵥ ι (fun a => bk.ev c * y a)) i ∈ bk.OE
      have : ι (fun a => bk.ev c * y a) = bk.evW c • ι y := by funext a; simp [ι, BK.evW]
      rw [this, Matrix.mulVec_smul]; exact Subring.mul_mem _ (hevW c) (hy i))
    (fun y hy i => by
      have h : (M⁻¹ *ᵥ ι (fun a => (l : Ainf l) * y a)) i ∈ bk.OE := hy i
      have : ι (fun a => (l : Ainf l) * y a) = ((l : ℕ) : WCb l) • ι y := by funext a; simp [ι]
      rw [this, Matrix.mulVec_smul] at h
      exact hOEcl.1 _ h)
    (fun y hy _ z hz i => by
      refine hOEcl.2.1 _ fun n => ⟨_, hy n i, ?_⟩
      rw [← Pi.sub_apply, ← Matrix.mulVec_sub]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.dvd_sum fun j _ => Dvd.dvd.mul_left ?_ _
      have := map_dvd (inclW l) (hz n j)
      simpa [ι, map_sub, map_pow, map_natCast] using this)
    Y1 M (by rw [hY1M, Matrix.det_mul]; exact (hMu.mul hVu).ne_zero)
    ((Matrix.isUnit_iff_isUnit_det M).2 hMu) hmemV
    (fun y hy => by
      refine ⟨M⁻¹ *ᵥ ι y, hy, ?_⟩
      show ι y = M *ᵥ (M⁻¹ *ᵥ ι y)
      rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec])
  obtain ⟨Wm, hWm⟩ : ∃ Wm : Matrix (Fin d) (Fin d) (WCb l), Wm = M⁻¹ * Y.map (inclW l) := ⟨_, rfl⟩
  have hYWm : Y.map (inclW l) = M * Wm := by rw [hWm, ← Matrix.mul_assoc, hMM, Matrix.one_mul]
  have hcol : ∀ (A : Matrix (Fin d) (Fin d) (Ainf l)) (j : Fin d),
      (A *ᵥ fun a => bk.ev ((Pi.single j (1 : bk.S) : Fin d → bk.S) a)) = fun i => A i j := by
    intro A j; funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hWmOE : ∀ i j, Wm i j ∈ bk.OE := by
    intro i j
    have h : (M⁻¹ *ᵥ ι (fun a => Y a j)) i ∈ bk.OE := (hYmem (fun a => Y a j)).2 ⟨Pi.single j (1 : bk.S), (hcol Y j).symm⟩ i
    rw [hWm]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, ι] using h
  have hC : ∀ j, ∃ c : Fin d → bk.S, (fun i => Y1 i j) = Y *ᵥ fun a => bk.ev (c a) := fun j =>
    (hYmem _).1 (by rw [← hcol Y1 j]; exact hmemV _)
  choose c hc using hC
  obtain ⟨Cw, hCw⟩ : ∃ Cw : Matrix (Fin d) (Fin d) (WCb l), Cw = Matrix.of fun a j => bk.evW (c j a) := ⟨_, rfl⟩
  have hVW : V = Wm * Cw := by
    have h1 : Y1.map (inclW l) = Y.map (inclW l) * Cw := by
      refine Matrix.ext fun i j => ?_
      have := congrArg (fun v => inclW l (v i)) (hc j)

      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hCw, BK.evW, map_sum] using this
    rw [hY1M, hYWm, Matrix.mul_assoc] at h1
    have h2 := congrArg (HMul.hMul M⁻¹) h1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMM', Matrix.one_mul, Matrix.one_mul] at h2
    exact h2
  refine ⟨Y, Wm, Cw * V', hYu, hWmOE, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [Matrix.mul_apply, hCw, Matrix.of_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hevW _) (hV' k j)
  · rw [← Matrix.mul_assoc, ← hVW, hVV']
  · rw [hYWm, hM, Matrix.smul_mul]
  · rintro y ⟨w, hw, hyw⟩
    refine (hYmem y).1 ?_
    intro i
    have : ι y = M *ᵥ w := by
      rw [hM]; refine hyw.trans ?_; funext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    show (M⁻¹ *ᵥ ι y) i ∈ bk.OE
    rw [this, Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec]; exact hw i

end GlobalTheory.BKLim.SatLat
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.exists_powerSeries_lift_of_period_pow_smul_integral_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d d' M : ℕ) (X : Matrix (Fin d') (Fin d) (WCb l)) (x : Matrix (Fin d') (Fin d) (Ainf l)), (∀ i j, X i j ∈ bk.OE) → x.map (inclW l) = inclW l τ ^ M • X → ∃ Y : Matrix (Fin d') (Fin d) bk.S, Y.map bk.evW = X := by
  first | exact @GlobalTheory.BSP.KisinFF.main | exact GlobalTheory.BSP.KisinFF.main | (intros; apply GlobalTheory.BSP.KisinFF.main <;> assumption)
end
