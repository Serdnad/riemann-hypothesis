module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealX
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle049
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.LatHat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSKfOrb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstPf

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal ComplexConjugate

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

def refNg : {n r k : ℕ} → n = 2 * r + k + 1 → (ε : Fin n → Bool) → (Fin r → Fin n → ℂ) → (Fin r → Fin n → ℂ) →
    (Fin k → Fin n → ℂ) → (Fin n → ℂ) → Measure (Formalism.REAL.UJ ε)
  | _, _, _, rfl, ε, e, f, wf, z0 => refN ε e f wf z0

theorem refNg_rfl {r k : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 : Fin (2 * r + k + 1) → ℂ) :
    refNg rfl ε e f wf z0 = refN ε e f wf z0 := rfl

theorem muSL_smul {n : ℕ} {ε : Fin n → Bool} (μH μN : Measure (Formalism.REAL.UJ ε)) [SFinite μH] (c : ℝ≥0∞) :
    muSL μH (c • μN) = c • muSL μH μN := by
  unfold muSL; rw [Measure.prod_smul_left, Measure.map_smul]
  exact measurable_mul.aemeasurable

theorem disint_smul_right {n r k : ℕ} {ε : Fin n → Bool} {T T' : ℝ} {μS μS' : Measure (Formalism.REAL.UJ ε)}
    {h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε} {C c : ℝ} (hc : 0 < c) (hD : DisintLoc ε k T T' μS μS' h C) :
    DisintLoc ε k T T' μS (ENNReal.ofReal c • μS') h (C / c) := by
  intro φ hφ
  rw [hD φ hφ]
  refine setLIntegral_congr_fun (JL.measurableSet_goodLoc r T T') (fun x _ => ?_)
  simp_rw [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← ENNReal.ofReal_mul' hc.le]
  congr 2
  field_simp

theorem placeStep (hJG : JacGauge) {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool)
    (e f : Fin r → Fin n → ℂ) (wf : Fin k → Fin n → ℂ) (z z' : Fin n → ℂ) {T T' : ℝ} (hk : 1 ≤ k) (hT : 0 < T)
    (hT' : 0 < T') (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0)
    (hez' : ∀ a, hJ ε (e a) z' = 0) (hfz' : ∀ a, hJ ε (f a) z' = 0) (hzz' : hJ ε z' z' = -(T' : ℂ))
    (hG : Formalism.MainNotions.S.Gauge.GaugeDens ε) (μH μH' : Measure (Formalism.REAL.UJ ε))
    (hH : IsHaarLoc (Formalism.L2.SG.Pf.NcReal.HLoc ε e f z) μH) (hH' : IsHaarLoc (Formalism.L2.SG.Pf.NcReal.HLoc ε e f z') μH')
    (a a' : ℝ) (ha : 0 < a) (ha' : 0 < a') (hma : μH Set.univ = ENNReal.ofReal a)
    (hma' : μH' Set.univ = ENNReal.ofReal a') (κ κ' : ℝ) (hκ : 0 < κ) (hκ' : 0 < κ')
    (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) (hh : IsSecLoc ε 1 e z z' T T' h) :
    DisintLoc ε k T T' (muSL μH (ENNReal.ofReal κ • refNg hn ε e f wf (z0v T z)))
      (muSL μH' (ENNReal.ofReal κ' • refNg hn ε e f wf (z0v T z))) h
      (Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
        ((T * T') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * (κ * κ'))) := by
  subst hn
  have hs : (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ * T = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hT.le, inv_mul_cancel₀ hT.ne']
  have hsC : ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * (T : ℂ) = 1 := by exact_mod_cast hs
  have hFJ : IsFrameJ ε e f wf (z0v T z) :=
    { ee := hee, ff := hff, ef := hef
      ez := fun a => by rw [z0v, JL.hJ_smul_r, hez, mul_zero]
      fz := fun a => by rw [z0v, JL.hJ_smul_r, hfz, mul_zero]
      zz := by
        rw [z0v, JL.hJ_smul_l, JL.hJ_smul_r, hzz, Complex.conj_ofReal]
        linear_combination (-1 : ℂ) * hsC
      ww := hww, ew := hew, fw := hfw
      zw := fun a => by rw [z0v, JL.hJ_smul_l, hzw, mul_zero] }
  have hzB : inWb k r (zBv k r T) := inWb_zB T
  have hQzB : Qm e f wf (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  have hTzB : Tz k r (zBv k r T) = T := Tz_zB hT.le
  set zB' := Qi ε e f wf (z0v T z) *ᵥ z' with hzB'
  have hQzB' : Qm e f wf (z0v T z) *ᵥ zB' = z' := by
    rw [hzB', Matrix.mulVec_mulVec, Qm_mul_Qi hFJ, Matrix.one_mulVec]
  have hzB'W : inWb k r zB' := by
    intro i hi
    rcases hi with hi | hi
    · have hie : i = eI k r ⟨i.val, hi⟩ := Fin.ext rfl
      rw [hie, hzB', Qi_mulVec_eI, hfz']
    · exact Qi_perp z' hez' i hi
  have hTzB' : Tz k r zB' = T' := by
    have hw := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_P (gramQ hFJ) zB' zB'
    rw [hQzB', hzz'] at hw
    unfold Tz
    rw [← hw]
    simp
  have hHB : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf (z0v T z) *ᵥ zBv k r T)) μH := by
    rw [hQzB]; exact hH
  have hHB' : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf (z0v T z) *ᵥ zB')) μH' := by
    rw [hQzB']; exact hH'
  have hhB : IsSecLoc ε 1 e (Qm e f wf (z0v T z) *ᵥ zBv k r T) (Qm e f wf (z0v T z) *ᵥ zB')
      (Tz k r (zBv k r T)) (Tz k r zB') h := by
    rw [hQzB, hQzB', hTzB, hTzB']; exact hh
  have hD := jacLocX_of hJG k r ε e f wf (z0v T z) (zBv k r T) zB' hFJ hk hzB hzB'W (by rw [hTzB]; exact hT)
    (by rw [hTzB']; exact hT') hG μH μH' hHB hHB' a a' ha ha' hma hma' κ hκ h hhB
  rw [hTzB, hTzB'] at hD
  have hD2 := disint_smul_right (c := κ' / κ) (div_pos hκ' hκ) hD
  haveI : SigmaFinite μH' := hH'.1
  have hm : muSL μH' (ENNReal.ofReal κ' • refN ε e f wf (z0v T z)) =
      ENNReal.ofReal (κ' / κ) • muSL μH' (ENNReal.ofReal κ • refN ε e f wf (z0v T z)) := by
    rw [muSL_smul, muSL_smul, smul_smul, ← ENNReal.ofReal_mul (div_pos hκ' hκ).le, div_mul_cancel₀ _ hκ.ne']
  show DisintLoc ε k T T' (muSL μH (ENNReal.ofReal κ • refN ε e f wf (z0v T z)))
    (muSL μH' (ENNReal.ofReal κ' • refN ε e f wf (z0v T z))) h _
  rw [hm]
  convert hD2 using 1
  have hV1 := Jac.volU_pos (k - 1)
  field_simp

theorem refNg_isHaarLoc {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool)
    (e f : Fin r → Fin n → ℂ) (wf : Fin k → Fin n → ℂ) (z z' : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0) (hez' : ∀ a, hJ ε (e a) z' = 0) :
    IsHaarLoc (NLoc ε e z') (refNg hn ε e f wf (z0v T z)) := by
  subst hn
  have hs : (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ * T = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hT.le, inv_mul_cancel₀ hT.ne']
  have hsC : ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * (T : ℂ) = 1 := by exact_mod_cast hs
  have hFJ : IsFrameJ ε e f wf (z0v T z) :=
    { ee := hee, ff := hff, ef := hef
      ez := fun a => by rw [z0v, JL.hJ_smul_r, hez, mul_zero]
      fz := fun a => by rw [z0v, JL.hJ_smul_r, hfz, mul_zero]
      zz := by
        rw [z0v, JL.hJ_smul_l, JL.hJ_smul_r, hzz, Complex.conj_ofReal]
        linear_combination (-1 : ℂ) * hsC
      ww := hww, ew := hew, fw := hfw
      zw := fun a => by rw [z0v, JL.hJ_smul_l, hzw, mul_zero] }
  have hQzB : Qm e f wf (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  have hz0 : ∃ t : ℂ, z0v T z = t • (Qm e f wf (z0v T z) *ᵥ zBv k r T) :=
    ⟨(((Real.sqrt T)⁻¹ : ℝ) : ℂ), by rw [hQzB]; rfl⟩
  have h0 := refN_isHaarLoc hFJ (inWb_zB T) hz0
  rw [hQzB] at h0
  obtain ⟨h1, h2, h3, h4⟩ := h0
  have hNeq : NLoc ε e z' = NLoc ε e z := by
    ext g
    exact ⟨fun hg => inN_indep hez hg, fun hg => inN_indep hez' hg⟩
  show IsHaarLoc (NLoc ε e z') (refN ε e f wf (z0v T z))
  rw [hNeq]
  exact ⟨h1, h2, h3, h4⟩

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
  Matrix Formalism.L2.SG.Pf.NcS.KfOrbPf
open scoped TensorProduct

section OEvRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem oev_inclR (o : 𝓞 E) : inclR (F := F) (Fv F v) (o : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨o, trivial, rfl⟩

theorem oev_one : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  have h := oev_inclR (F := F) (E := E) v 1
  simpa using h

theorem oev_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  unfold OEv at hx hy ⊢
  rw [SetLike.mem_coe] at hx hy ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨b, -, rfl⟩ := hb
      exact Submodule.subset_span ⟨a * b, trivial, by simp [map_mul]⟩
    | zero => simp
    | add y z _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h =>
      show _ * ((c : Fv F v) • y) ∈ _
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c h
  | zero => simp
  | add x z _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    show ((c : Fv F v) • x) * y ∈ _
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c h

theorem sigR_smul' (σ : E →ₐ[F] E) (c : Fv F v) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, TensorProduct.smul_tmul']
  | add x y h1 h2 => rw [smul_add, map_add (f := _), h1, h2, map_add (f := _), smul_add]

theorem oev_sigR (σ : E →ₐ[F] E) {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    sigR (Fv F v) σ x ∈ OEv (E := E) v := by
  unfold OEv at hx ⊢
  rw [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    refine Submodule.subset_span
      ⟨⟨σ a, map_isIntegral_int σ (RingOfIntegers.isIntegral_coe a)⟩, trivial, ?_⟩
    simp [sigR, inclR]
    rfl
  | zero => simp
  | add x y _ _ h1 h2 => rw [map_add (f := _)]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    show sigR (Fv F v) σ ((c : Fv F v) • x) ∈ _
    rw [sigR_smul']
    exact Submodule.smul_mem _ c h

def oevRing : Subring (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  mul_mem' := oev_mul v
  one_mem' := oev_one v
  add_mem' := fun hx hy => Submodule.add_mem _ hx hy
  zero_mem' := Submodule.zero_mem _
  neg_mem' := fun hx => Submodule.neg_mem _ hx

theorem mem_std_of_oev {n : ℕ} (y : Fin n → Fv F v ⊗[F] E) (hy : ∀ i, y i ∈ OEv (E := E) v) :
    y ∈ latLoc (E := E) v ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  have hsingle : ∀ (i : Fin n) (z : Fv F v ⊗[F] E), z ∈ OEv (E := E) v → Pi.single i z ∈ latLoc (E := E) v
      ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
    intro i z hz
    change z ∈ Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨o, -, rfl⟩ := hw
      refine Submodule.subset_span ⟨Pi.single i (o : E), ?_, ?_⟩
      · rw [SetLike.mem_coe, MassDataMassesW.KCptW.stdSub, Submodule.mem_pi]
        intro k _
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      · funext k
        by_cases hk : k = i
        · subst hk; simp [ratV]
        · simp [ratV, hk]
    | zero => rw [Pi.single_zero]; exact Submodule.zero_mem _
    | add w w' _ _ h1 h2 => rw [Pi.single_add]; exact Submodule.add_mem _ h1 h2
    | smul c w _ h =>
      have : (Pi.single i (c • w) : Fin n → Fv F v ⊗[F] E) = c • (Pi.single i w : Fin n → Fv F v ⊗[F] E) := by
        funext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      rw [this]
      exact Submodule.smul_mem _ c h
  rw [← Finset.univ_sum_single y]
  exact Submodule.sum_mem _ fun i _ => hsingle i (y i) (hy i)

theorem ev_oev (x : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, inclR (F := F) (Fv F v) x ∈ OEv (E := E) v := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsIntegral.isIntegral x).isAlgebraic
  obtain ⟨N, hN0, hNx⟩ := halg.exists_integral_multiple
  let o : 𝓞 E := ⟨N • x, hNx⟩
  filter_upwards [ev_int (F := F) ((N : F)⁻¹)] with v hv
  have e : inclR (F := F) (Fv F v) x =
      (⟨algebraMap F (Fv F v) ((N : F)⁻¹), hv⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (o : E) := by
    show _ = algebraMap F (Fv F v) ((N : F)⁻¹) • inclR (F := F) (Fv F v) (N • x)
    rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, map_zsmul, zsmul_eq_mul, ← mul_assoc, ← map_intCast (algebraMap F (Fv F v ⊗[F] E)), ← map_mul,
      inv_mul_cancel₀ (Int.cast_ne_zero.2 hN0), map_one, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ (oev_inclR v o)

theorem oev_smul' {r : Fv F v} (hr : r ∈ v.adicCompletionIntegers F) {z : Fv F v ⊗[F] E}
    (hz : z ∈ OEv (E := E) v) : r • z ∈ OEv (E := E) v :=
  Submodule.smul_mem _ (⟨r, hr⟩ : v.adicCompletionIntegers F) hz

end OEvRing

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.EC

open Formalism.QuantumDeterminants WlocSk.NB

theorem expChart_of (hS : ShearStep) (hC : ConstStep) : ExpChart := by
  intro k r
  obtain ⟨σ, hσ, hσe⟩ := hS k r
  obtain ⟨Λ, hΛm, hΛ, hvol⟩ := hC k r
  have hE := Formalism.MainNotions.BridgeCSB.continuous_expLie (k := k) (r := r) (Nset k r)
  let Φ : (CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => phi0 t.1 t.2
  have hφ : Continuous Φ := continuous_nilpotent_chart
  unfold Formalism.MainNotions.S.haarLie
  rw [one_smul, hvol, Measure.map_smul, Measure.map_map hE.measurable hΛm, ← hσ.map_eq]
  congr 1
  have e : ((fun x : Formalism.MainNotions.S.lieE (Nset k r) => fun i j =>
      NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j) ∘ Λ : (J k r → ℝ) → Mt k r) = Φ ∘ σ := by
    funext y
    simp only [Function.comp, Φ]
    rw [hσe y, hΛ y, Formalism.MainNotions.BridgeCSB.unrealify_RL]
  rw [e]
  exact (Measure.map_map hφ.measurable hσ.measurable).symm
  exact hE.measurable.aemeasurable

end Formalism.L2.SG.Pf.NcReal.JX.EC

namespace Formalism.L2.SG.Pf.NcReal.JX

theorem exponential_chart_haar : ExpChart := EC.expChart_of EC.shear_change_holds EC.constant_change_holds

end Formalism.L2.SG.Pf.NcReal.JX
end
end
