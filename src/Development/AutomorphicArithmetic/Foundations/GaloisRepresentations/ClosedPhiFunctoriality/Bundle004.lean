module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle636
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle606
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle605
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.zeroAp_holds :
    ZeroAp := by
  intro l _ K bk c M
  obtain ⟨htor, -, -, hphi, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.primePow_dvd_tiltUniformizer_pow_acris_eventually l K bk c M
  refine ⟨c * n₀ + M, ?_⟩
  intro d d' D F F' hdiv hcong
  have hdiv' : ∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ D i j := hdiv
  set u := ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X with hu
  have hφu : phiA l u = u ^ l := by
    rw [hu, RingHom.comp_apply, hphi, ← bk.ev_frob]
    have : frobS l bk.a X = X ^ l := by simp [frobS]
    rw [this, map_pow, map_pow]
  have hφl : ∀ k : ℕ, phiA l ((l : Per.Acris l) ^ k) = (l : Per.Acris l) ^ k := by
    intro k; simp
  set P : Per.Acris l := (l : Per.Acris l) ^ (c * n₀ + M) with hP
  have hφP : phiA l P = P := hφl _
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin d) (Fin d') (Per.Acris l),
      (l : Per.Acris l) ^ c • D = F * D.map (phiA l) * F' + P • G := by
    refine ⟨Matrix.of fun i j => (hcong i j).choose, ?_⟩
    ext i j
    have h := (hcong i j).choose_spec
    rw [Matrix.add_apply, Matrix.smul_apply (P), Matrix.of_apply, smul_eq_mul, ← h,
      Matrix.sub_apply]
    ring
  have key : ∀ t : ℕ, ∃ N H : Matrix (Fin d) (Fin d') (Per.Acris l),
      (l : Per.Acris l) ^ (c * t) • D = u ^ (l ^ t) • N + P • H := by
    intro t
    induction t with
    | zero =>
      refine ⟨Matrix.of fun i j => (hdiv' i j).choose, 0, ?_⟩
      ext i j
      simp only [mul_zero, pow_zero, pow_one, one_smul, smul_zero, add_zero, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul]
      rw [one_mul]
      exact (hdiv' i j).choose_spec
    | succ t ih =>
      obtain ⟨N, H, hNH⟩ := ih
      refine ⟨F * N.map (phiA l) * F', F * H.map (phiA l) * F' + (l : Per.Acris l) ^ (c * t) • G, ?_⟩
      have hmap : ((l : Per.Acris l) ^ (c * t) • D).map (phiA l)
          = (l : Per.Acris l) ^ (c * t) • D.map (phiA l) := by
        ext i j; simp [hφl]
      have hmap2 : (u ^ (l ^ t) • N + P • H).map (phiA l)
          = u ^ (l ^ (t + 1)) • N.map (phiA l) + P • H.map (phiA l) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _),
          map_mul, map_pow, hφu, hφP]
        rw [← pow_mul, pow_succ' l t]
      calc (l : Per.Acris l) ^ (c * (t + 1)) • D
          = (l : Per.Acris l) ^ (c * t) • ((l : Per.Acris l) ^ c • D) := by
            rw [smul_smul, ← pow_add, mul_add, mul_one]
        _ = F * (((l : Per.Acris l) ^ (c * t) • D).map (phiA l)) * F'
              + P • ((l : Per.Acris l) ^ (c * t) • G) := by
            rw [hG, hmap, smul_add, Matrix.mul_smul, Matrix.smul_mul, smul_comm P]
        _ = u ^ (l ^ (t + 1)) • (F * N.map (phiA l) * F')
              + P • (F * H.map (phiA l) * F' + (l : Per.Acris l) ^ (c * t) • G) := by
            rw [hNH, hmap2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
              Matrix.mul_smul, Matrix.smul_mul, smul_add, add_assoc]
  intro i j
  obtain ⟨N, H, hNH⟩ := key n₀
  obtain ⟨y, hy⟩ := hn₀ n₀ le_rfl
  have hent : (l : Per.Acris l) ^ (c * n₀) * D i j = u ^ (l ^ n₀) * N i j + P * H i j := by
    have := congrFun (congrFun hNH i) j
    simpa using this
  have hpos : 1 ≤ l ^ n₀ := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  have hsplit : u ^ (l ^ n₀) = u * u ^ (l ^ n₀ - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  refine ⟨u * y * N i j + H i j, ?_⟩
  apply GlobalTheory.CrZero.pow_cancel _ htor (c * n₀)
  rw [hent, hsplit, hy, hP, pow_add]
  ring
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trLim_holds :
    TrStep → TrLim := by
  intro hstep l _ P AI T K bk Γ _ _ L₀ a r Cl Cv s V V' p θ pv hs hV hV' hlink hθ
  by_contra hne
  have hpθ : p - θ ≠ 0 := sub_ne_zero.mpr hne
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hlnorm : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    have h := PadicAlgCl.norm_extends l ((l : ℚ_[l]))
    rw [Padic.norm_p] at h
    simpa using h
  have hnp : ∀ (c : ℕ) (x : Om l), ‖(l : Om l) ^ c * x‖ = ((l : ℝ) ^ c)⁻¹ * ‖x‖ := by
    intro c x
    rw [norm_mul, norm_pow, hlnorm, inv_pow]
  obtain ⟨c₁, hc₁⟩ := pow_unbounded_of_one_lt (‖p - θ‖ + ∑ i, ‖(Cv.b i).trace‖) hl1
  have hsmall : ∀ x : Om l, ‖x‖ ≤ ‖p - θ‖ + ∑ i, ‖(Cv.b i).trace‖ → ‖(l : Om l) ^ c₁ * x‖ ≤ 1 := by
    intro x hx
    rw [hnp, inv_mul_le_iff₀ (pow_pos hl0 c₁), mul_one]
    exact hx.trans hc₁.le
  have hsum0 : 0 ≤ ∑ i, ‖(Cv.b i).trace‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have ht : ∀ i, ‖(l : Om l) ^ c₁ * (Cv.b i).trace‖ ≤ 1 := fun i =>
    hsmall _ (((Finset.single_le_sum (f := fun i => ‖(Cv.b i).trace‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))).trans
      (le_add_of_nonneg_left (norm_nonneg _)))
  have hd : ‖(l : Om l) ^ c₁ * (p - θ)‖ ≤ 1 := hsmall _ (le_add_of_nonneg_right hsum0)
  have hpos : 0 < ‖(l : Om l) ^ c₁ * (p - θ)‖ := by
    rw [hnp]
    exact mul_pos (inv_pos.mpr (pow_pos hl0 c₁)) (norm_pos_iff.mpr hpθ)
  obtain ⟨c₂, hc₂⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
  have hc₂' : ((l : ℝ) ^ c₂)⁻¹ ≤ ‖(l : Om l) ^ c₁ * (p - θ)‖ := by
    rw [← inv_pow]
    exact hc₂.le
  have hdvd : ∀ M : ℕ, (l : Per.Acris l) ^ M ∣ (l : Per.Acris l) ^ c₂ * s := by
    intro M
    obtain ⟨m, hMm, hm⟩ := hlink M
    have hle : ((l : ℝ) ^ m)⁻¹ ≤ ((l : ℝ) ^ M)⁻¹ :=
      inv_anti₀ (pow_pos hl0 M) (pow_le_pow_right₀ hl1.le hMm)
    refine hstep l P AI T s Cv.d (Cv.tw.d' m) (Cv.lay m).m M c₁ c₂ (fun i => (Cv.b i).trace)
      (fun j k => ((Cv.lay m).b j k).trace) (Cv.lay m).c (pv m) p θ (Cv.tw.Pi m) Cv.e (Cv.lay m).e V (V' m)
      hV (hV' m) hm (fun i => (pow_dvd_pow _ hMm).trans (Cv.unit m i)) (fun j => ?_) ((hθ m).trans hle) ht hd hc₂'
    have h := Cv.trace m j
    rw [Matrix.trace_sum] at h
    simp only [Matrix.trace_smul, smul_eq_mul] at h
    exact h.trans hle
  obtain ⟨htor, hcomp, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  have hz := GlobalTheory.CrZero.eq_zero_of_forall_dvd _ hcomp.toIsHausdorff _ hdvd
  have hs0 : s = 0 := GlobalTheory.CrZero.pow_cancel (l : Per.Acris l) htor c₂ s 0 (by simpa using hz)
  haveI : Nontrivial P.R.B := GlobalTheory.Pst.nontrivial_B P
  haveI : Nontrivial (Per.Bcris l) := T.eB.injective.nontrivial
  rw [hs0, map_zero] at hs
  exact not_isUnit_zero hs
end
