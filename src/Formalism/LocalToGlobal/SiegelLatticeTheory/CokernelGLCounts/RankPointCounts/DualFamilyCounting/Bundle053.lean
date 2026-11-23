module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle052
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXLeb
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNMapKapL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CMeasSbox
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle048
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle049
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRb
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem refNBox_of (hF : FrameRow) : RefNBox := by
  intro D X u w
  choose L hL hdet using fun v => hF X u w v
  have hTu := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u
  have hTw := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) w
  have hdet0 : ∀ v, LinearMap.det (L v) ≠ 0 := fun v h0 => by
    have h1 := hdet v
    rw [h0, abs_zero] at h1
    exact (pow_pos (div_pos hTw hTu) _).ne' h1.symm
  have key : ∀ (s : X.B.I.Ginf) v i, LsNc5.kapV X w v s i =
      L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) (s v)) i := fun s v i => by
    have h1 := congrFun (hL v s) i
    rw [kapV_eq (X := X) u v s] at h1
    exact h1
  have hbox : LsNc5.boxN X w = X.NinfU w ∩ Set.univ.pi (fun v =>
      (fun g => L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) g)) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) := by
    rw [LsNc5.boxN_eq]
    congr 1
    ext s
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h v i
      rw [← key s v i]
      exact h (v, i)
    · rintro h ⟨v, i⟩
      show LsNc5.kapV X w v s i ∈ _
      rw [key s v i]
      exact h v i
  have hv : ∀ v, refNX X u v ((fun g => L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) g)) ⁻¹'
      Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) =
      ENNReal.ofReal ((2 : ℝ) ^ (D.R.rS ^ 2 + D.R.rS * D.R.k) * (Tw w ^ D.R.rS)⁻¹) := fun v => by
    obtain ⟨hae, hmap⟩ := refN_map_kapL (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v)
      (ProductExactness.zV X u v) hTu (fX_ee (X := X) (v := v)) (fX_ff (X := X) (v := v))
      (fX_ef (X := X) (v := v)) (fX_ww (X := X) (u := u) (v := v)) (fX_ew (X := X) (u := u) (v := v))
      (fX_fw (X := X) (u := u) (v := v)) (fX_ez (X := X) (u := u) (v := v))
      (fX_fz (X := X) (u := u) (v := v)) (frame_real_z_z_eq_neg (X := X) (u := u) (v := v))
      (fX_zw (X := X) (u := u) (v := v))
    have hmeas : MeasurableSet ((L v) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) :=
      (L v).continuous_of_finiteDimensional.measurable (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
    have hpre : (fun g => L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) g)) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1) =
        kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) ⁻¹' ((L v) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) := rfl
    rw [hpre, show refNX X u v = refNg (nX X) _ _ _ _ _ from rfl, ← Measure.map_apply_of_aemeasurable hae hmeas, hmap,
      Measure.smul_apply, smul_eq_mul, Measure.addHaar_preimage_linearMap _ (hdet0 v), Real.volume_pi_Ico]
    simp only [sub_zero, ENNReal.ofReal_one, Finset.prod_const_one, mul_one]
    rw [abs_inv, hdet v, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_pow]
    field_simp
  haveI : ∀ v, SigmaFinite (refNX X u v) := fun v =>
    (refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
      (ProductExactness.zV X u v) hTu (fX_ee (X := X) (v := v)) (fX_ff (X := X) (v := v))
      (fX_ef (X := X) (v := v)) (fX_ww (X := X) (u := u) (v := v)) (fX_ew (X := X) (u := u) (v := v))
      (fX_fw (X := X) (u := u) (v := v)) (fX_ez (X := X) (u := u) (v := v))
      (fX_fz (X := X) (u := u) (v := v)) (frame_real_z_z_eq_neg (X := X) (u := u) (v := v))
      (fX_zw (X := X) (u := u) (v := v)) (fX_ez (X := X) (u := u) (v := v))).1
  rw [hbox, Set.inter_comm, measure_inter_conull (refNX_haar X u w).2.2.1, Measure.pi_pi]
  simp only [hv, Finset.prod_const, Finset.card_univ]
  rw [← ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [inv_pow, ← inv_pow]
  ring

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section

noncomputable section

open MeasureTheory Matrix NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Inv

variable {r k : ℕ}

def RcInv (y : LsNc5.CIdx r k → ℝ) : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) :=
  (fun c => (⟨y (eIdx (Sum.inl (c, false))), y (eIdx (Sum.inl (c, true)))⟩ : ℂ), fun a => y (eIdx (Sum.inr a)))

theorem Rc_RcInv (y : LsNc5.CIdx r k → ℝ) : Rc (RcInv y) = y := by
  funext i
  obtain ⟨j, rfl⟩ := eIdx.surjective i
  rcases j with ⟨c, b⟩ | a
  · cases b <;> simp [Rc, RcInv, LsNc5.reim]
  · simp [Rc, RcInv]

theorem measurable_RcInv : Measurable (RcInv (r := r) (k := k)) := by
  apply Continuous.measurable
  unfold RcInv
  have h : Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) := Complex.equivRealProdCLM.symm.continuous
  exact Continuous.prodMk (continuous_pi fun c => h.comp'
      (f := fun a : LsNc5.CIdx r k → ℝ => (a (eIdx (Sum.inl (c, false))), a (eIdx (Sum.inl (c, true)))))
      ((continuous_apply _).prodMk (continuous_apply _)))
    (continuous_pi fun a => continuous_apply _)

def dYInv (T : ℝ) (y : LsNc5.CIdx r k → ℝ) : LsNc5.CIdx r k → ℝ := fun i => y i / dY T i

theorem dY_pos {T : ℝ} (hT : 0 < T) (i : LsNc5.CIdx r k) : 0 < dY T i := by
  rcases i with (a | a) | a <;> simp [dY, hT]

theorem LyM_dYInv {T : ℝ} (hT : 0 < T) (y : LsNc5.CIdx r k → ℝ) : LyM T (dYInv T y) = y := by
  funext i
  simp only [LyM, Matrix.toLin'_apply, Matrix.mulVec_diagonal, dYInv]
  field_simp [(dY_pos hT i).ne']

theorem measurable_dYInv (T : ℝ) : Measurable (dYInv (r := r) (k := k) T) := by
  unfold dYInv
  exact Measurable.of_eval fun i => (measurable_pi_apply i).div_const _

end Inv

theorem surjLoc {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (w : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (w a) = 0) (hfw : ∀ c a, hJ ε (f c) (w a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (w a) = 0) :
    ∃ σL : (LsNc5.CIdx r k → ℝ) → Formalism.REAL.UJ ε, Measurable σL ∧
      ∀ y, σL y ∈ NLoc ε e z ∧ kapL ε e f w z (σL y) = y := by
  subst hn
  have hFJ := isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have emb := embQ hFJ
  have hQz : Qm e f w (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  set Ψ := cM (ε := ε) (Qi ε e f w (z0v T z)) (Qm e f w (z0v T z)) with hΨ
  let ψ0 : (LsNc5.CIdx r k → ℝ) → (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) := fun y => RcInv (dYInv T y)
  have hψ0 : Measurable ψ0 := measurable_RcInv.comp (measurable_dYInv T)
  let Φ : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => WlocSk.NB.phi0 t.1 t.2
  have hΦc : Continuous Φ := WlocSk.NB.continuous_nilpotent_chart
  have hΦN : ∀ t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ), WlocSk.NB.phi0 t.1 t.2 ∈ Nset k r := fun t =>
    WlocSk.NB.test_vector_mem_schwartz_bruhat t.1 t.2
  have hrange : ∀ t, Φ t ∈ Set.range Ψ := fun t => by
    refine ⟨toUJ _ (conjQ_UJ hFJ (hΦN t).1), ?_⟩
    show (Qi ε e f w (z0v T z) * uMat (toUJ _ (conjQ_UJ hFJ (hΦN t).1)) * Qm e f w (z0v T z) :
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 t.1 t.2
    rw [uMat_toUJ, Qi_Qm_conj hFJ]
  let σL : (LsNc5.CIdx r k → ℝ) → Formalism.REAL.UJ ε := fun y => emb.equivRange.symm ⟨Φ (ψ0 y), hrange (ψ0 y)⟩
  have hσΨ : ∀ y, Ψ (σL y) = Φ (ψ0 y) := fun y => by
    have h1 := emb.equivRange.apply_symm_apply ⟨Φ (ψ0 y), hrange (ψ0 y)⟩
    rw [MeasurableEmbedding.equivRange_apply] at h1
    exact congrArg Subtype.val h1
  have hz0 : ∃ t : ℂ, z0v T z = t • (Qm e f w (z0v T z) *ᵥ zBv k r T) :=
    ⟨(((Real.sqrt T)⁻¹ : ℝ) : ℂ), by rw [hQz]; rfl⟩
  refine ⟨σL, ?_, fun y => ⟨?_, ?_⟩⟩
  · exact emb.equivRange.symm.measurable.comp
      ((hΦc.measurable.comp hψ0).subtype_mk)
  · have hN : Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) ∈ Nset k r := by
      have : (Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 (ψ0 y).1 (ψ0 y).2 := hσΨ y
      rw [this]; exact hΦN _
    have h1 := inN_of_conj hFJ (inWb_zB T) hN
    rw [hQz] at h1
    exact h1
  · have hN : Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) ∈ Nset k r := by
      have : (Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 (ψ0 y).1 (ψ0 y).2 := hσΨ y
      rw [this]; exact hΦN _
    rw [kapL_eq hFJ hT (σL y) hN]
    show Kc T (Ψ (σL y)) = y
    rw [hσΨ y]
    funext i
    rw [chart_kappa_coordinates T (ψ0 y) i, ← LyM_apply]
    show LyM T (Rc (RcInv (dYInv T y))) i = y i
    rw [Rc_RcInv, LyM_dYInv hT]

theorem kapSurj_holds : KapSurj := by
  intro D X u
  have hloc := fun v : InfinitePlace X.B.I.F => surjLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v)
    (ProductExactness.zV X u v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
    (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v)
  choose σL hσm hσ using hloc
  refine ⟨fun t v => σL v (fun i => Φc t (v, i)), ?_, fun t => ⟨fun v => (hσ v _).1, ?_⟩⟩
  · exact Measurable.of_eval fun v => (hσm v).comp
      (Measurable.of_eval fun i => (measurable_pi_apply (v, i)).comp measurable_Φc)
  · have hk : Φc (blk X u (fun v => σL v (fun i => Φc t (v, i)))) = Φc t := by
      rw [← kap_eq_Φc]
      funext p
      have := (hσ p.1 (fun i => Φc t (p.1, i))).2
      have h2 := congrFun (kapV_eq X u p.1 (fun v => σL v (fun i => Φc t (v, i)))) p.2
      exact h2.trans (congrFun this p.2)
    have := congrArg Ψc hk
    rwa [Ψc_Φc, Ψc_Φc] at this

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.TrD

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace DetH

variable {D : D7}

theorem eq_zero_of_trace {t : D.host.E}
    (h : ∀ o : 𝓞 D.host.E, Algebra.trace ℚ D.host.E (t * o) = 0) : t = 0 := by
  refine (traceForm_nondegenerate ℚ D.host.E).1 t fun e => ?_
  have halg : IsAlgebraic ℤ e :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsIntegral.isIntegral (R := ℚ) e).isAlgebraic
  obtain ⟨y, hy0, hyi⟩ := halg.exists_integral_multiple
  have h1 : Algebra.trace ℚ D.host.E (t * (y • e)) = 0 := h ⟨y • e, hyi⟩
  rw [mul_smul_comm, map_zsmul, zsmul_eq_mul] at h1
  rw [Algebra.traceForm_apply]
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd (by exact_mod_cast h2) hy0
  · exact h2

variable (X : HidaSetting D)

theorem eq_zero_of_trB {x : (VS D).V} (hx : x ∈ X.Lb)
    (h : ∀ y ∈ X.Lb, Algebra.trace ℚ D.host.E ((VS D).hT x y) = 0) : x = 0 := by
  have h1 : ∀ y ∈ X.Lb, (VS D).hT x y = 0 := fun y hy => eq_zero_of_trace fun o => by
    have h2 := h (o • y) (X.Lb.smul_mem o hy)
    rwa [← algebraMap_smul D.host.E o y, LinearMap.map_smul, smul_eq_mul, mul_comm] at h2
  have hxW := (mem_Wb X).1 (Lb_le_alt X hx)
  have he : ∀ c, (VS D).hT x (X.eX c) = 0 := fun c => by
    rw [herm_swap (X.eX c) x, (hxW c).1, star_zero]
  have hf : ∀ c, (VS D).hT x (X.fY c) = 0 := fun c => by
    rw [herm_swap (X.fY c) x, (hxW c).2, star_zero]
  have h2 : ∀ y ∈ (VS D).L0, (VS D).hT x y = 0 := by
    intro y hy
    obtain ⟨α, β, l, hl, rfl⟩ := decomp X hy

    simp [map_add (f := _), map_sum, map_smul, he, hf, h1 l hl]
  have hle : Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) ≤ LinearMap.ker ((VS D).hT x) :=
    Submodule.span_le.2 fun y hy => LinearMap.mem_ker.2 (h2 y hy)
  refine (VS D).nondeg.1 x fun v => ?_
  have hv : v ∈ Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) := by
    let a : Fin X.B.I.n → X.B.I.E := fun i => X.ιE.symm (X.bas.repr v i)
    have ha : a ∈ Submodule.span X.B.I.E (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
      rw [X.B.I.L_span]; trivial
    have hm : ∀ z ∈ Submodule.span X.B.I.E (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)),
        (∑ i, X.ιE (z i) • X.bas i) ∈ Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span ((X.L_eq z).1 hz)
      | zero => simp
      | add z w hz hw ihz ihw => simpa [map_add, add_smul, Finset.sum_add_distrib] using Submodule.add_mem _ ihz ihw
      | smul c z hz ih => simpa [map_mul, mul_smul, Finset.smul_sum] using Submodule.smul_mem _ (X.ιE c) ih
    have := hm a ha
    simpa only [a, RingEquiv.apply_symm_apply, X.bas.sum_repr] using this
  exact LinearMap.mem_ker.1 (hle hv)

theorem trB_expand {N : ℕ} (ℓ : Module.Basis (Fin N) ℤ (X.Lb.restrictScalars ℤ)) (x y : (VS D).V) (hy : y ∈ X.Lb) :
    Algebra.trace ℚ D.host.E ((VS D).hT x y) =
      ∑ i, ((ℓ.repr ⟨y, hy⟩ i : ℤ) : ℚ) * Algebra.trace ℚ D.host.E ((VS D).hT x (ℓ i : (VS D).V)) := by
  have e : y = ∑ i, (ℓ.repr ⟨y, hy⟩ i) • (ℓ i : (VS D).V) := by
    have h := congrArg Subtype.val (ℓ.sum_repr ⟨y, hy⟩)
    rw [Submodule.coe_sum] at h
    simpa [Submodule.coe_smul] using h.symm
  conv_lhs => rw [e]
  exact trB_sum_right _ _ _

end DetH


open DetH in
theorem detHOne_holds : DetHOne := by
  intro D X N ℓ ℓs
  have hGi : ∀ m i, ∃ z : ℤ,
      Algebra.trace ℚ D.host.E ((VS D).hT (ℓ m : (VS D).V) (ℓ i : (VS D).V)) = z := fun m i =>
    (Lb_le_Ldual X (ℓ m).2).2 _ (ℓ i).2
  choose Gz hGz using hGi
  have hHi : ∀ k j, ∃ z : ℤ,
      Algebra.trace ℚ D.host.E ((VS D).hT (ℓs k : (VS D).V) (ℓ j : (VS D).V)) = z := fun k j =>
    (ℓs k).2.2 _ (ℓ j).2
  choose Hz hHz using hHi
  set G : Matrix (Fin N) (Fin N) ℤ := Matrix.of Gz with hG
  set H : Matrix (Fin N) (Fin N) ℤ := Matrix.of Hz with hH
  have hind : LinearIndependent ℤ (fun m => (ℓ m : (VS D).V)) :=
    ℓ.linearIndependent.map' (X.Lb.restrictScalars ℤ).subtype (Submodule.ker_subtype _)

  have hcomb : ∀ (a : Fin N → ℤ) (i : Fin N),
      Algebra.trace ℚ D.host.E ((VS D).hT (∑ m, a m • (ℓ m : (VS D).V)) (ℓ i : (VS D).V)) =
        ((Matrix.vecMul a G) i : ℚ) := by
    intro a i
    rw [trB_sum_left]
    simp only [hGz, Matrix.vecMul, dotProduct, hG, Matrix.of_apply]
    push_cast; rfl
  have hmem : ∀ a : Fin N → ℤ, ∑ m, a m • (ℓ m : (VS D).V) ∈ X.Lb := fun a =>
    Submodule.sum_mem _ fun m _ => Submodule.smul_of_tower_mem _ _ (ℓ m).2

  have hdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨a, ha0, ha⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    have hx : ∑ m, a m • (ℓ m : (VS D).V) = 0 := by
      refine eq_zero_of_trB X (hmem a) fun y hy => ?_
      rw [trB_expand X ℓ _ y hy]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hcomb, ha]; simp
    exact ha0 (funext fun m => Fintype.linearIndependent_iff.1 hind a hx m)
  have hdetQ : ((G.det : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hdet

  set r : ℚ := ((G.det : ℤ) : ℚ)⁻¹ with hr
  let xs : Fin N → (VS D).V := fun j => ((r : ℚ) : D.host.E) • ∑ m, G.adjugate j m • (ℓ m : (VS D).V)
  have hpair : ∀ j (y : (VS D).V), Algebra.trace ℚ D.host.E ((VS D).hT (xs j) y) =
      r * Algebra.trace ℚ D.host.E ((VS D).hT (∑ m, G.adjugate j m • (ℓ m : (VS D).V)) y) := by
    intro j y
    simp only [xs, LinearMap.map_smulₛₗ₂, smul_eq_mul]
    rw [map_ratCast, ← Rat.smul_def, LinearMap.map_smul, smul_eq_mul]
  have hdual : ∀ j i, Algebra.trace ℚ D.host.E ((VS D).hT (xs j) (ℓ i : (VS D).V)) =
      ((1 : Matrix (Fin N) (Fin N) ℤ) j i : ℚ) := by
    intro j i
    rw [hpair, hcomb]
    have hv : (Matrix.vecMul (G.adjugate j) G) i = (G.adjugate * G) j i := rfl
    rw [hv, Matrix.adjugate_mul, Matrix.smul_apply, smul_eq_mul, Int.cast_mul, hr, ← mul_assoc,
      inv_mul_cancel₀ hdetQ, one_mul]
  have hxsW : ∀ j, xs j ∈ Ldual X := by
    intro j
    refine ⟨(Wb X).smul_mem _ (Lb_le_alt X (hmem _)), fun y hy => ?_⟩
    refine ⟨ℓ.repr ⟨y, hy⟩ j, ?_⟩
    rw [trB_expand X ℓ _ y hy]
    simp only [hdual, Matrix.one_apply]
    push_cast
    simp

  let C : Matrix (Fin N) (Fin N) ℤ := Matrix.of fun j k => ℓs.repr ⟨xs j, hxsW j⟩ k
  have hCH : C * H = 1 := by
    ext j i
    have e : xs j = ∑ k, C j k • (ℓs k : (VS D).V) := by
      have h := congrArg Subtype.val (ℓs.sum_repr ⟨xs j, hxsW j⟩)
      rw [Submodule.coe_sum] at h
      simpa [C, Submodule.coe_smul] using h.symm
    have h1 := hdual j i
    rw [e, trB_sum_left] at h1
    simp only [hHz] at h1
    have h2 : (((C * H) j i : ℤ) : ℚ) = ((1 : Matrix (Fin N) (Fin N) ℤ) j i : ℚ) := by
      rw [← h1, Matrix.mul_apply]; push_cast; simp [hH]
    exact_mod_cast h2
  have hHC : H.det * C.det = 1 := by rw [mul_comm, ← Matrix.det_mul, hCH, Matrix.det_one]
  have hunit : IsUnit H.det := ⟨⟨H.det, C.det, hHC, by rw [mul_comm]; exact hHC⟩, rfl⟩
  have hmat : (Matrix.of fun k j => Algebra.trace ℚ D.host.E ((VS D).hT (ℓs k : (VS D).V) (ℓ j : (VS D).V))) =
      H.map (Int.cast : ℤ → ℚ) := by
    ext k j; simp [hH, hHz]
  have hdH : (H.map (Int.cast : ℤ → ℚ)).det = ((H.det : ℤ) : ℚ) := by
    simpa using (RingHom.map_det (Int.castRingHom ℚ) H).symm
  rw [hmat, hdH]
  rcases Int.isUnit_iff.1 hunit with h | h <;> simp [h]

end Formalism.L2.SG.Pf.NcReal.JX.CovB.TrD
end
end
