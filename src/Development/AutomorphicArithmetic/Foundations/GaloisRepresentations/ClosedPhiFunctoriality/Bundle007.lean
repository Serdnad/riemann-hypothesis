module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle661
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle606
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle745
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle082
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle557
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle758
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle731
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaConjBoundedCompatibleBreuilKisinFrames
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix GlobalTheory.CrTop
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem invQ_holds : InvQ := by
  intro l _ K bk τ hτ N k d ρ F hcr Q Q' hsec g
  obtain ⟨hQQ, hQu₀, hQ'u₀, hQφ₀⟩ := hsec
  obtain ⟨Y, Y', hY, hYY⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) F.toPre
  obtain ⟨-, -, hE2⟩ := GlobalTheory.T.frame_ainf_matrix_frobenius_galois_eqs l K bk τ hτ N d (fun g => (ρ g).val) F Y Y' hY hYY
  obtain ⟨htf, -, ⟨v, hv⟩, hφι, hσι⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  set ι := algebraMap (Ainf l) (Per.Acris l) with hι
  have hQu : ∀ i j, ι (bk.ev X) ∣ (Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j := hQu₀
  have hQ'u : ∀ i j, ι (bk.ev X) ∣ (Q' - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j := hQ'u₀
  change (F.ε g).map (fun a => ι (WittVector.frobenius a)) * Q.map (sigA (g : GQ l)) = Q
  set σ := sigA (g : GQ l) with hσdef
  set fA : bk.S →+* Per.Acris l := (ι.comp bk.ev).comp (frobS l bk.a) with hfA
  set f0 : bk.S →+* Per.Acris l := fA.comp ((PowerSeries.C).comp PowerSeries.constantCoeff) with hf0
  have hQφ : fA bk.E ^ N • (Q * F.A.map f0) = f0 bk.E ^ N • (F.A.map fA * Q.map (phiA l)) := hQφ₀
  set ε' := (F.ε g).map (fun a => ι (WittVector.frobenius a)) with hε'
  have hfr : ∀ s : bk.S, fA s = ι (WittVector.frobenius (bk.ev s)) := fun s => by
    simp only [hfA, RingHom.comp_apply, bk.ev_frob]
  have hfix : ∀ c : Wq l bk.a, σ (fA (PowerSeries.C c)) = fA (PowerSeries.C c) := fun c => by
    rw [hfr, hσdef, hσι, ← GlobalTheory.RingBasics.φA_apply, ← ActLaws.φA_σA, bk.ev_C, bk.gal_w g c]
  have hcomm : ∀ x, phiA l (σ x) = σ (phiA l x) := fun x => GlobalTheory.CrisMaps.phiA_sigA (g : GQ l) x
  have he₀ : ∃ w : (Per.Acris l)ˣ, f0 bk.E = (l : Per.Acris l) * w := by
    obtain ⟨w, hw⟩ := bk.coeff_zero
    have hc : PowerSeries.constantCoeff bk.E = (l : Wq l bk.a) * w := by
      rw [← hw]; simp
    refine ⟨((Units.map (PowerSeries.C (R := Wq l bk.a)).toMonoidHom w).map fA.toMonoidHom), ?_⟩
    simp [hf0, hc]
  have hBB : F.A.map fA * F.A'.map fA = fA bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    rw [← Matrix.map_mul, F.A_mul, map_smul_ring, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
  have hAA : F.A.map f0 * F.A'.map f0 = f0 bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    rw [← Matrix.map_mul, F.A_mul, map_smul_ring, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
  have hσA₀ : (F.A.map f0).map σ = F.A.map f0 := by
    ext i j; simp only [Matrix.map_apply, hf0, RingHom.comp_apply]; exact hfix _
  have hσe₀ : σ (f0 bk.E) = f0 bk.E := by simp only [hf0, RingHom.comp_apply]; exact hfix _
  have hσf : ∀ s : bk.S, ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev s))) = σ (fA s) := fun s => by
    rw [hfr, hσdef, hσι, ← GlobalTheory.RingBasics.φA_apply, ← GlobalTheory.RingBasics.φA_apply, ActLaws.φA_σA]
  have h2 : fA bk.E ^ N • (ε' * (F.A.map fA).map σ) = σ (fA bk.E) ^ N • (F.A.map fA * ε'.map (phiA l)) := by
    have e := congrArg (fun M => M.map (ι.comp WittVector.frobenius)) (hE2 g)
    simp only [map_smul_ring, Matrix.map_mul, Matrix.map_map, map_pow, RingHom.comp_apply] at e
    have hm1 : F.A.map (fun s => ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev s)))) =
        (F.A.map fA).map σ := by
      ext i j
      exact hσf _
    have hm2 : F.A.map (fun s => ι (WittVector.frobenius (bk.ev s))) = F.A.map fA := by
      ext i j
      exact (hfr _).symm
    have hm3 : (F.ε g).map (fun a => ι (WittVector.frobenius (WittVector.frobenius a))) =
        ε'.map (phiA l) := by
      ext i j
      exact (hφι _).symm
    change ι (WittVector.frobenius (bk.ev bk.E)) ^ N •
      (ε' * F.A.map (fun s => ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev s))))) =
      ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev bk.E))) ^ N •
      (F.A.map (fun s => ι (WittVector.frobenius (bk.ev s))) *
        (F.ε g).map (fun a => ι (WittVector.frobenius (WittVector.frobenius a)))) at e
    rw [← hfr, hσf, hm1, hm2, hm3] at e
    exact e
  have hL1 := GlobalTheory.T.frobenius_equation_of_twisted_cocycle_defect (Per.Acris l) (phiA l) σ d N k (l : Per.Acris l) (fA bk.E) (f0 bk.E) Q Q' (F.A.map fA) (F.A'.map fA)
    (F.A.map f0) (F.A'.map f0) ε' htf ⟨v, hv⟩ he₀ hcomm (map_natCast _ _) (map_natCast _ _) hσe₀ hσA₀ hQQ hBB hAA hQφ h2
  obtain ⟨w₀, hw₀⟩ := he₀
  set D := Q' * ε' * Q.map σ - (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) with hD
  have hDeq : (l : Per.Acris l) ^ (2 * N) • D = F.A.map f0 * D.map (phiA l) * (((w₀⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) ^ (2 * N) • F.A'.map f0) := by
    rw [Matrix.mul_smul, ← hL1, smul_smul, hw₀]
    congr 1
    rw [mul_pow, mul_left_comm, ← mul_pow, Units.inv_mul, one_pow, mul_one]
  set u := ι (bk.ev X) with hu
  set π := Ideal.Quotient.mk (Ideal.span {u}) with hπ
  have hz : ∀ M : Matrix (Fin d) (Fin d) (Per.Acris l), (∀ i j, u ∣ M i j) ↔ M.map π = 0 := fun M => by
    constructor
    · intro h; ext i j
      simpa [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using h i j
    · intro h i j
      have := congrFun (congrFun h i) j
      simpa [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using this
  have hQ1 : Q.map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
    rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 hQu
  have hQ'1 : Q'.map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
    rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 hQ'u
  have hdvdφ : bk.ev X ∣ WittVector.frobenius (bk.ev X) := by
    rw [bk.ev_X, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
    exact dvd_pow_self _ (Fact.out : l.Prime).ne_zero
  have hε1 : ε'.map π = 1 := by
    have : ∀ i j, u ∣ (ε' - 1) i j := fun i j => by
      obtain ⟨c, hc⟩ := hcr g i j
      have e1 : (ε' - 1) i j = ι (WittVector.frobenius ((F.ε g - 1) i j)) := by
        simp only [hε', Matrix.sub_apply, Matrix.map_apply, map_sub]
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
      rw [e1, hc, map_mul, map_mul]
      exact dvd_mul_of_dvd_left (map_dvd ι hdvdφ) _
    rw [← sub_eq_zero, ← Matrix.map_one π (map_zero _) (map_one _), ← Matrix.map_sub _ (map_sub π)]
    exact (hz _).1 this
  have hQσ : (Q.map σ).map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
    have hdσ : u ∣ σ u := by
      rw [hu, hσdef, hσι]; exact map_dvd ι ((galois_discMap l K bk).1 (g : GQ l))
    have : ∀ i j, u ∣ (Q.map σ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j := fun i j => by
      have e1 : (Q.map σ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j =
          σ ((Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j) := by
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
      obtain ⟨c, hc⟩ := hQu i j
      rw [e1, hc, map_mul]
      exact dvd_mul_of_dvd_left hdσ _
    rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 this
  have hdiv : ∀ i j, ι (bk.ev X) ∣ D i j := by
    refine (hz D).2 ?_
    rw [hD, Matrix.map_sub _ (map_sub π), Matrix.map_mul, Matrix.map_mul, hQ'1, hε1, hQσ]
    simp only [map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _), mul_one, smul_mul_smul_comm, map_pow]
    rw [← pow_add, ← two_mul, sub_self]
  have hD0 := GlobalTheory.T.acris_frobenius_matrix_eq_zero_of_dvd l K bk d (2 * N) D (F.A.map f0) _ hdiv hDeq
  have hM : Q' * ε' * Q.map σ = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) :=
    sub_eq_zero.1 hD0
  refine smul_cancel (pow_cancel htf (2 * k)) ?_
  have := congrArg (fun M => Q * M) hM
  simp only [← Matrix.mul_assoc, hQQ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at this
  exact this

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem link_core {W : Type} [CommRing W] (fr : W →+* W) (c e : W) (hc : fr c = c) {d d' : ℕ}
    (Z Rv : Matrix (Fin d) (Fin d') W) (T A : Matrix (Fin d) (Fin d) W) (T' A' : Matrix (Fin d') (Fin d') W)
    (hZ : Z.map fr = Z) (hT : IsUnit T) (hφ : e • T.map fr = T * A) (hφ' : e • T'.map fr = T' * A')
    (hD : ∀ i j, c ∣ (Z * T' - T * Rv) i j) :
    ∀ i j, c ∣ (Rv * A' - A * Rv.map fr) i j := by
  choose G hG using hD
  have hD' : Z * T' - T * Rv = c • Matrix.of G := by
    ext i j
    simp [hG i j]
  have h1 : Z * T'.map fr - T.map fr * Rv.map fr = c • (Matrix.of G).map fr := by
    have h := congrArg (fun M => M.map fr) hD'
    have e1 : (Z * T' - T * Rv).map fr = Z * T'.map fr - T.map fr * Rv.map fr := by
      rw [Matrix.map_sub _ (map_sub fr), Matrix.map_mul, Matrix.map_mul, hZ]
    have e2 : (c • Matrix.of G).map fr = c • (Matrix.of G).map fr := by
      ext i j
      simp [hc]
    simpa only [e1, e2] using h
  have h2 : T * (Rv * A' - A * Rv.map fr) = c • (e • (Matrix.of G).map fr - Matrix.of G * A') := by
    have e3 : T * Rv = Z * T' - c • Matrix.of G := by rw [← hD']; abel
    calc T * (Rv * A' - A * Rv.map fr)
        = (T * Rv) * A' - (T * A) * Rv.map fr := by
          rw [Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Z * (T' * A') - c • (Matrix.of G * A') - (T * A) * Rv.map fr := by
          rw [e3, Matrix.sub_mul, Matrix.mul_assoc, Matrix.smul_mul]
      _ = e • (Z * T'.map fr - T.map fr * Rv.map fr) - c • (Matrix.of G * A') := by
          rw [← hφ, ← hφ', Matrix.mul_smul, Matrix.smul_mul, smul_sub]
          abel
      _ = c • (e • (Matrix.of G).map fr - Matrix.of G * A') := by
          rw [h1, smul_sub, smul_comm]
  obtain ⟨u, rfl⟩ := hT
  have h3 : Rv * A' - A * Rv.map fr =
      c • ((↑u⁻¹ : Matrix (Fin d) (Fin d) W) * (e • (Matrix.of G).map fr - Matrix.of G * A')) := by
    rw [← Matrix.mul_smul, ← h2, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  intro i j
  rw [h3, Matrix.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

private theorem pow_dvd_of_ev {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (n : ℕ) (x : bk.S)
    (h : (l : Ainf l) ^ n ∣ bk.ev x) : (l : bk.S) ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := h
    obtain ⟨x', rfl⟩ := bk.dvd_of_dvd_ev x ⟨(l : Ainf l) ^ n * c, by rw [hc, pow_succ', mul_assoc]⟩
    have h0 : bk.ev x' - (l : Ainf l) ^ n * c = 0 := by
      apply ainf_torsionFree
      rw [map_mul, map_natCast, pow_succ', mul_assoc] at hc
      rw [mul_sub, hc, sub_self]
    have h1 : (l : Ainf l) ^ n ∣ bk.ev x' := ⟨c, sub_eq_zero.1 h0⟩
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih x' h1)

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.linkA_holds :
    LinkA := by
  intro l _ K bk τ hτ N d d' n ρ ρ' F F' Y Y' hY hY' Pi R hlink
  have hev : ∀ s, inclW l (bk.ev s) = bk.evW s := fun s => rfl
  refine ⟨?_, ?_⟩
  · intro i j
    apply GlobalTheory.HTBound.pow_dvd_of_inclW
    have e1 : (Pi.map (Per.zA l)).map (inclW l) = zW Pi := by
      refine Matrix.ext fun a b => ?_
      exact (inclWA l).commutes _
    have e2 : (R.map bk.ev).map (inclW l) = R.map bk.evW := by
      rw [Matrix.map_map]; rfl
    have e : (Pi.map (Per.zA l) * Y' - Y * R.map bk.ev).map (inclW l) =
        inclW l τ ^ N • (zW Pi * F'.T - F.T * R.map bk.evW) := by
      rw [Matrix.map_sub _ (map_sub (inclW l)), Matrix.map_mul, Matrix.map_mul, hY, hY', e1, e2,
        Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    have := congrFun (congrFun e i) j
    rw [Matrix.map_apply] at this
    rw [this, Matrix.smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_left (hlink i j) _
  · have key := link_core (frobW l).toRingHom ((l : WCb l) ^ n) (bk.evW bk.E ^ N) (by simp)
      (zW Pi) (R.map bk.evW) F.T (F.A.map bk.evW) F'.T (F'.A.map bk.evW)
      (by ext i j; simp [zW]) F.unit F.φ F'.φ hlink
    have hfr : (R.map bk.evW).map (frobW l).toRingHom = (R.map (frobS l bk.a)).map bk.evW := by
      refine Matrix.ext fun a b => ?_
      simp only [Matrix.map_apply]
      show frobW l (inclW l (bk.ev (R a b))) = inclW l (bk.ev (frobS l bk.a (R a b)))
      rw [frobW_inclW, bk.ev_frob]
    rw [hfr] at key
    have hmap : R.map bk.evW * F'.A.map bk.evW - F.A.map bk.evW * (R.map (frobS l bk.a)).map bk.evW =
        (R * F'.A - F.A * R.map (frobS l bk.a)).map bk.evW := by
      rw [Matrix.map_sub _ (map_sub bk.evW), Matrix.map_mul, Matrix.map_mul]
    rw [hmap] at key
    intro i j
    apply pow_dvd_of_ev
    apply GlobalTheory.HTBound.pow_dvd_of_inclW
    simpa only [Matrix.map_apply, hev] using key i j
end
