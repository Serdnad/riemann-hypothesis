module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle661
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle606
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle745
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle636
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle605
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle082
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle557
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle603
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle184
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle746
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinModuleTensorBdRPlusEqLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle628
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle747
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle631

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CrTop

theorem map_smul_ring {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ} (c : R)
    (M : Matrix (Fin d) (Fin d) R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

theorem pow_cancel {R : Type} [CommRing R] {lr : R} (h : ∀ x : R, lr * x = 0 → x = 0) (n : ℕ) :
    ∀ x : R, lr ^ n * x = 0 → x = 0 := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih => intro x hx; exact ih x (h _ (by rw [← mul_assoc, ← pow_succ']; exact hx))

theorem smul_cancel {R : Type} [CommRing R] {c : R} (h : ∀ x : R, c * x = 0 → x = 0) {d : ℕ}
    {M M' : Matrix (Fin d) (Fin d) R} (hM : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun hM i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact sub_eq_zero.1 (h _ (by rw [mul_sub, this, sub_self]))

theorem crys_of_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val), F.IsCr → IsCrys (P.PD K) (qRep ρ) := by
  intro l _ K bk τ hτ P AI T N d ρ F hcr
  obtain ⟨Y, Y', hY, hYY⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) F.toPre
  obtain ⟨-, hR1, hE2⟩ := GlobalTheory.T.frame_ainf_matrix_frobenius_galois_eqs l K bk τ hτ N d (fun g => (ρ g).val) F Y Y' hY hYY
  obtain ⟨k, Q, Q', hQQ, hQu, hQ'u, hQφ⟩ := GlobalTheory.T.exists_frobenius_section_acris_breuilKisin l K bk N d F.A F.A' F.A_mul
  obtain ⟨htf, -, ⟨v, hv⟩, hφι, hσι⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  set ι := algebraMap (Ainf l) (Per.Acris l) with hι

  have key : ∀ g : ↥(GK K), (F.ε g).map (fun a => ι (WittVector.frobenius a)) * Q.map (sigA (g : GQ l)) = Q := by
    intro g
    set σ := sigA (g : GQ l) with hσdef
    set fA : bk.S →+* Per.Acris l := (ι.comp bk.ev).comp (frobS l bk.a) with hfA
    set f0 : bk.S →+* Per.Acris l := fA.comp ((PowerSeries.C).comp PowerSeries.constantCoeff) with hf0
    set ε' := (F.ε g).map (fun a => ι (WittVector.frobenius a)) with hε'
    have hfr : ∀ s : bk.S, fA s = ι (WittVector.frobenius (bk.ev s)) := fun s => by
      simp only [hfA, RingHom.comp_apply, bk.ev_frob]
    have hfix : ∀ c : Wq l bk.a, σ (fA (PowerSeries.C c)) = fA (PowerSeries.C c) := fun c => by
      rw [hfr, hσdef, hσι, ← GlobalTheory.RingBasics.φA_apply, ← ActLaws.φA_σA, bk.ev_C, bk.gal_w g c]
    have hcomm : ∀ x, phiA l (σ x) = σ (phiA l x) := fun x => by
      simp only [hσdef]
      exact GlobalTheory.CrisMaps.phiA_sigA (g : GQ l) x
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
      have hfrfun : (fA : bk.S → Per.Acris l) = (fun s => ι (WittVector.frobenius (bk.ev s))) := funext hfr
      simpa only [hε', Matrix.map_map, RingHom.coe_comp, Function.comp_def, RingHom.comp_apply, hfrfun, hσf, hφι] using e
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
  obtain ⟨U, hU, hinv⟩ := GlobalTheory.T.exists_invariant_unit_matrix_bcris_frame l K bk τ hτ N d k ρ Y Y' F.ε Q Q' hYY hR1 hQQ key
  exact GlobalTheory.T.isCrystalline_of_invariant_unit_bcris_matrix l K P AI T d ρ U hU hinv

end GlobalTheory.CrTop
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open Filter
open scoped TensorProduct InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift.TermCont

open GlobalTheory.RawLift

theorem continuous_lagTerm : ∀ D : D7, ∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr,
    SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ →
      ∀ Y : Lag W, Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ →
        Continuous fun g : GA D W => lagTerm μ 𝓕 (fr Y) (om (1, g) f₁) f₂ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ f₂ h₁ h₂ Y _
  have hw := hS.weil
  have hψ := hw.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ h₂
  have hJ := GlobalTheory.ThetaJointCont.continuous_om_oriented hw h₁
  have hrm : ∀ (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E), Continuous fun u : WO V W => ratMul C u := fun C => by
    unfold ratMul
    exact continuous_const.matrix_mul continuous_id
  have hμ1 : μ 𝓕 = 1 := hS.covol.2.2
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [hμ1]; exact ENNReal.one_ne_top)
  have : SecondCountableTopology (GA D W) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W).2.1
  refine continuous_iff_continuousAt.2 fun g₀ => ?_

  have hc0 : Continuous fun w : WO V W => om ((1 : GA D V), g₀) f₁ w :=
    hJ.comp (continuous_const.prodMk continuous_id)
  obtain ⟨κ, hκ⟩ := hK.exists_bound_of_continuousOn hc0.continuousOn
  have hev : ∀ᶠ g in 𝓝 g₀, ∀ w ∈ K, ‖om ((1 : GA D V), g) f₁ w‖ ≤ κ + 1 := by
    refine hK.eventually_forall_of_forall_eventually fun w hw' => ?_
    have hc : Continuous fun y : GA D W × WO V W => ‖om ((1 : GA D V), y.1) f₁ y.2‖ :=
      (hJ.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)).norm
    exact (hc.continuousAt.eventually_lt continuousAt_const ((hκ w hw').trans_lt (lt_add_one κ))).mono
      fun y hy => hy.le
  have hall : ∀ᶠ g in 𝓝 g₀, ∀ w, ‖om ((1 : GA D V), g) f₁ w‖ ≤ κ + 1 := hev.mono fun g hg w => by
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← GlobalTheory.OrientedHeis.theta_norm_periodic hψ (hw.om_pres _ f₁ h₁) γ hγ w]
    exact hg _ h
  unfold lagTerm
  refine continuousAt_of_dominated (bound := fun _ => (κ + 1) * C₂) ?_ ?_ (integrable_const _) ?_
  · refine Eventually.of_forall fun g => ?_
    exact ((((hw.om_pres _ f₁ h₁).cont.comp (hrm _)).mul
      (continuous_star.comp (h₂.cont.comp (hrm _))))).aestronglyMeasurable
  · refine hall.mono fun g hg => Eventually.of_forall fun u => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hg _) (hC₂ _) (norm_nonneg _) ((norm_nonneg _).trans (hg 0))
  · refine Eventually.of_forall fun u => ?_
    exact ((hw.om_cont f₁ h₁ _).comp (continuous_const.prodMk continuous_id)).continuousAt.mul continuousAt_const

end GlobalTheory.RawLift.TermCont

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.lagrangians_transverse_eq_graphs_rational_unitary : ∀ (D : D7) (W : HSp D), ∃ e : GQ W ≃ {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥},
    ∀ γ : GQ W, ∃ c : Matrix (Fin W.rank) (Fin W.rank) D.host.E, mt W (γ : GA D W) = c.map (incA D) ∧ IsLagFrame W (e γ).1 (1, c) := by
  first | exact @GlobalTheory.RawLift.Graphs.graphs | exact GlobalTheory.RawLift.Graphs.graphs | (intros; apply GlobalTheory.RawLift.Graphs.graphs <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.rallis_inner_product_kernel_identity : ∀ D : D7, KerAbs D → SWPair D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ h, IntegrableOn (fun g => star (thetaKO om h g f₁) * φ₁ g) 𝓖 νW) ∧ IntegrableOn (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) 𝓗 νV ∧ ∫ h in 𝓗, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂νV = ((νV 𝓗).toReal : ℂ) * ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  first | exact @GlobalTheory.RawLift.rallis_kernel_step | exact GlobalTheory.RawLift.rallis_kernel_step | (intros; apply GlobalTheory.RawLift.rallis_kernel_step <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.siegelWeil_lagrangian_term_stronglyMeasurable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsWeilDatumO ψ V W χV χW om → IsCovolOne (ratL W V) μ 𝓕 → ∀ (f₁ f₂ : WO V W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E, StronglyMeasurable (fun p : GA D W × GA D W => lagTerm μ 𝓕 C (om (1, p.1) f₁) (om (1, p.2) f₂)) := by
  first | exact @GlobalTheory.RallisMeas.lagTerm_stronglyMeasurable | exact GlobalTheory.RallisMeas.lagTerm_stronglyMeasurable | (intros; apply GlobalTheory.RallisMeas.lagTerm_stronglyMeasurable <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.countable_doubled_hermitian_lagrangians : ∀ (D : D7) (W : HSp D), Countable (Lag W) := by
  first | exact @GlobalTheory.RawLift.lag_countable | exact GlobalTheory.RawLift.lag_countable | (intros; apply GlobalTheory.RawLift.lag_countable <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.exists_isotropicFrame_lagrangian_first_summand : ∀ (D : D7) (W : HSp D) (Y : Lag W), Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ → ∃ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I ∧ Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) := by
  first | exact @GlobalTheory.RawLift.exists_isoFrame_comap_inl | exact GlobalTheory.RawLift.exists_isoFrame_comap_inl | (intros; apply GlobalTheory.RawLift.exists_isoFrame_comap_inl <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.kisinModule_tensor_bdRPlus_eq_lattice : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T), ∃ jD : (ι → OD l O) ≃ₗ[OD l O] TW (OD l O) T, ∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z → jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z := by
  first | exact @GlobalTheory.DeRhamIdent.main | exact GlobalTheory.DeRhamIdent.main | (intros; apply GlobalTheory.DeRhamIdent.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.jB_single_mem_filT' : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (C : GlobalTheory.MemLoc.Core l) (i : ι), R.jB (Pi.single i 1) ∈ filT C T (-(η : ℤ)) := by
  first | exact @GlobalTheory.BKGal.XiPole.jB_single_mem_filT | exact GlobalTheory.BKGal.XiPole.jB_single_mem_filT | (intros; apply GlobalTheory.BKGal.XiPole.jB_single_mem_filT <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.mu_pow_smul_acrisLattice_mem_acrisTensor : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ ε : OCb l, IsEps ε → ∀ z : ι → OCr l O, ∃ w : TW (OCr l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (fun i => toOB l O (z i)) = TWincl (toOB l O) T w := by
  first | exact @GlobalTheory.BKGal.CrisInt.mu_pow_smul_mem | exact GlobalTheory.BKGal.CrisInt.mu_pow_smul_mem | (intros; apply GlobalTheory.BKGal.CrisInt.mu_pow_smul_mem <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.isExactTriple_breuilKisin_of_shortExactLattices : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (μ : Type) [Fintype μ] [DecidableEq μ] (P₀ : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (P₁ : PhiMod ↥(OL LL) ↥LL.1 l e a κ) (P₂ : PhiMod ↥(OL LL) ↥LL.1 l e a μ) (T₀ T₁ T₂ : QLat LL) (I₀ : Ident (thetaW a LL) ϖ P₀ T₀) (I₁ : Ident (thetaW a LL) ϖ P₁ T₁) (I₂ : Ident (thetaW a LL) ϖ P₂ T₂) (f : LatHom T₀.L T₁.L) (g : LatHom T₁.L T₂.L) (F : GlobalTheory.BK.Hom P₀ P₁) (G : GlobalTheory.BK.Hom P₁ P₂), IsSESLat (Qp := ℚ_[l]) f g → IsMapOf I₀ I₁ f F → IsMapOf I₁ I₂ g G → IsExactTriple F G := by
  first | exact @GlobalTheory.BKExact.isExactTriple_of_isSESLat | exact GlobalTheory.BKExact.isExactTriple_of_isSESLat | (intros; apply GlobalTheory.BKExact.isExactTriple_of_isSESLat <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal


theorem _root_.GlobalTheory.T.coord_E_pow_basis_alt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (ε δ : OCb l), IsEps ε → δ ^ l = ε → ∀ j : ι, ∃ c : ι → OA l O, inclL t ϖ D.toPhiMod c = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) ∧ ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η)) • R.jB (fun i => toB l O (c i)) = TWincl (toB l O) T (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H • z) := by
  first | exact @GlobalTheory.BKGal.HatVal.coord_E_pow_basis | exact GlobalTheory.BKGal.HatVal.coord_E_pow_basis | (intros; apply GlobalTheory.BKGal.HatVal.coord_E_pow_basis <;> assumption)
end
