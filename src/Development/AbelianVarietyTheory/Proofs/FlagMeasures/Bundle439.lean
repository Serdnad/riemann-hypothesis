module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle331
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle435
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle436
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle393
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle332
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle408
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle306
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle199
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle254
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle051
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle132
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle056
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.StdChar
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
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.CovDom
open Formalism.L2.SG.PoincareInHH.PoincareSetting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem formallyUnramified_host (D : D7) : Algebra.FormallyUnramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  have : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) :=
    Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
      obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv
          (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
        RingOfIntegers.ext ht.symm
      rwa [this]
  infer_instance

theorem cancel_conj {m : ℕ} (A M N : Matrix (Fin m) (Fin m) ℂ) (hA : IsUnit A.det)
    (h : A * M * A⁻¹ = A * N * A⁻¹) : M = N := by
  have key : ∀ Z : Matrix (Fin m) (Fin m) ℂ, A⁻¹ * (A * Z * A⁻¹) * A = Z := by
    intro Z
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hA, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA,
      Matrix.one_mul]
  rw [← key M, h, key N]

theorem isDomN (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word) :
    GlobalTheory.SnMass.IsDomN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Lc X) (Pc X u) (Ac X C)
      (Gm D '' (trX X C '' Y.FN u)) := by
  obtain ⟨hmeas, hex, huniq⟩ := Y.FN_fund u
  obtain ⟨hsurj, hinj, hmul⟩ := GlobalTheory.T.transport_real_points_bijective_multiplicative D X θ C
  obtain ⟨h8a, h8b⟩ := GlobalTheory.T.integralUnipotent_eq_latticeUnipotent_coords D X θ C u
  have hgrp := Formalism.L2.SG.Pf.IdMeet.noinfEqC_holds D X u Y.hK
  have hA : ∀ w, IsUnit (Ac X C w).det := by
    intro w
    have h1 := (GlobalTheory.T.bessel_transport_isometry_frame_adapted D X θ C u).1 w
    have h2 := (GlobalTheory.T.concrete_gram_hermitian_nondegenerate_lattice_selfDual D X).1.2
    have e : ((Jc X).map w.embedding).det = w.embedding (Jc X).det := by rw [RingHom.map_det]; rfl
    have h3 : ((Jc X).map w.embedding).det ≠ 0 := by rw [e]; exact (map_ne_zero _).2 h2
    rw [← h1, Matrix.det_mul, Matrix.det_mul] at h3
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul h3)
  refine ⟨GlobalTheory.T.measurableSet_transported_real_points_image D X θ C _ hmeas, fun x hx => ?_⟩
  obtain ⟨g, rfl⟩ := hsurj x hx
  obtain ⟨s, hs, hsg⟩ := hex g
  obtain ⟨γ, hγ, hc⟩ := h8b s hs
  refine ⟨γ, ⟨hγ, trX X C (s * g), ⟨s * g, hsg, rfl⟩, ?_⟩, ?_⟩
  · funext w
    rw [hc w, ← hmul]
    simp
  · rintro γ' ⟨hγ', y, ⟨f, hf, rfl⟩, hy⟩
    obtain ⟨s', hs', hc'⟩ := h8a γ' hγ'
    have hfe : f = s' * g := by
      apply hinj
      funext w
      have := congrFun hy w
      simp only at this ⊢
      rw [this, hc' w, ← hmul]
      simp
    have hmem : s' * s⁻¹ ∈ NOinf X u := by
      rw [hgrp] at hs hs' ⊢
      exact Subgroup.mul_mem _ hs' (Subgroup.inv_mem _ hs)
    have hss : s' * s⁻¹ = 1 := huniq (s * g) hsg _ hmem (by rw [show s' * s⁻¹ * (s * g) = s' * g by group, ← hfe]; exact hf)
    have hs'e : s' = s := by rw [mul_inv_eq_one] at hss; exact hss
    subst hs'e
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.E) := inferInstance
    have hm := cancel_conj _ _ _ (hA w) ((hc' w).trans (hc w).symm)
    refine Matrix.ext fun i j => w.embedding.injective ?_
    have := congrFun (congrFun hm i) j
    simpa only [Matrix.map_apply] using this

theorem main : ∀ (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), (Measure.pi (fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal = (2 * D.host.v) ^ (((D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) * D.R.k + (D.R.rS : ℝ) / 2) * Fintype.card D.what₂.Tau) := by
  intro D X Y θ C u
  obtain ⟨hs, hnum⟩ := GlobalTheory.T.fundamental_domain_normalising_constants D
  obtain ⟨hH, hSD⟩ := GlobalTheory.T.concrete_gram_hermitian_nondegenerate_lattice_selfDual D X
  obtain ⟨hF, hDu, hT⟩ := GlobalTheory.T.wordFrame_dualTuple_gram_integrality D X u
  obtain ⟨hM, hAd⟩ := GlobalTheory.T.bessel_transport_isometry_frame_adapted D X θ C u
  have hI := GlobalTheory.T.covolume_integral_unipotentRadical_real_points D.host.F D.host.E D.sp.cm.sig D.R.k D.R.rS (Jc X) (Lc X) (Pc X u) (fc X) (Tc u)
    (Ac X C) (sc D) (GlobalTheory.AdelicU.isCMExt_host D) (formallyUnramified_host D) hH hSD hF hDu hT hM hs hAd
  have h1 := hI.2 _ (isDomN D X Y θ C u)
  have hv : 0 ≤ 2 * D.host.v := by unfold Host.v Host.rdE; positivity
  change (Measure.pi _ (trX X C '' Y.FN u)).toReal = _
  rw [← GlobalTheory.T.measurePi_pointsAtInfinitePlacesCMType_image D, h1, hnum, ENNReal.toReal_ofReal (Real.rpow_nonneg hv _)]

end GlobalTheory.CovDom
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.St.Rescale

theorem rescaleStep3 :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ D : Formalism.BasicNotions.D7, GlobalTheory.St.RescaleStep3 D := by
  intro hSW D X hb hM
  obtain ⟨hCM, hH, hsize, hfr⟩ := GlobalTheory.CmHermitianRankFrames.cm_herm_rank_frames D X
  obtain ⟨hA, hC⟩ := GlobalTheory.St.siegelWeil_volumes hSW X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH
  obtain ⟨ψ, hψ, hstd⟩ := Formalism.L2.SG.Pf.standard_character_exists X.B.I.F hCM.1
  have hstd' : Formalism.L2.SG.LocVol.IsStdChar ψ := hstd
  have hG := X.measG_norm
  have hμG : X.measG.μG.IsHaarMeasure := hG.1
  have hherm : ∀ {a : ℕ} (X0 : Fin a → Fin X.B.I.n → X.B.I.E) (i j : Fin a),
      X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J X0 j i) = gramE X.B.I.cm.sig X.B.I.J X0 i j :=
    fun X0 i j => GlobalTheory.FrameGram.hE_swap (GlobalTheory.FrameGram.conj_invol hCM) hH.1 _ _

  have hB : ∀ X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E,
      ∃ μ' : Measure (stabT (AF X.B.I.F) X.B.I.cm.sig X.B.I.J X0), μ'.IsHaarMeasure ∧
        ((gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0 →
          ∃ (hTB : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J X0 j i) =
              gramE X.B.I.cm.sig X.B.I.J X0 i j) (νB : Measure _),
            Formalism.L2.SG.Volumes.IsOmT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ _ hTB νB ∧
            Formalism.L2.SG.Volumes.IsCompatT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J X0 X.measG.μG μ' νB) := by
    intro X0
    by_cases hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0
    · obtain ⟨νX, μ', h1, h2, h3⟩ := GlobalTheory.T.exists_adelicTorusMeasure_stabiliserHaar X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH hA hC ψ hψ
        (2 * D.R.rS + 2) (by omega) (by omega) X0 (hherm X0) hdet X.measG.μG hμG
      exact ⟨μ', h2, fun _ => ⟨hherm X0, νX, h1, h3⟩⟩
    · exact ⟨X.measG.μB X0, hG.2.2.2.2.1 X0, fun h => absurd h hdet⟩
  choose μB' hμB' hBc using hB

  have hW : ∀ u, ∃ W : MeasW X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.TypedSets.frameOf X u), W.IsTextNorm ∧
      W.μNinf = (X.measW u).μNinf ∧ W.μHinf = (X.measW u).μHinf ∧
      (∃ (hT1 : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) j i) =
            gramE X.B.I.cm.sig X.B.I.J (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) i j) (νH : Measure _),
        Formalism.L2.SG.Volumes.IsOmT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ _ hT1 νH ∧
        Formalism.L2.SG.Volumes.IsCompatT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J
          (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) X.measG.μG W.μH νH) ∧
      covol W.μN = 1 ∧
      ∀ v, Formalism.L2.SG.LocVol.LocTieW X.B.I.cm.sig X.B.I.J ψ v (Formalism.L2.SG.TypedSets.frameOf X u)
        (X.measG.μGv v) (W.μSv v) := by
    intro u
    obtain ⟨T, hP⟩ := hfr u
    obtain ⟨hdet, hT1, -⟩ := GlobalTheory.FrameGram.std_frame_gram X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH
      D.R.rS (Formalism.L2.SG.TypedSets.frameOf X u) T hP
    obtain ⟨νH, μH, h1, h2, h3⟩ := GlobalTheory.T.exists_adelicTorusMeasure_stabiliserHaar X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH hA hC ψ hψ
      (D.R.rS + 1 + D.R.rS) (by omega) (by omega) (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) hT1 hdet
      X.measG.μG hμG
    obtain ⟨μN, hN, hN1⟩ := GlobalTheory.T.exists_haarMeasure_unipotentRadical_covolume_one X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH D.R.rS
      (Formalism.L2.SG.TypedSets.frameOf X u) T hP
    have hS : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F),
        ∃ μS : Measure (Ssub (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.TypedSets.frameOf X u)),
          μS.IsHaarMeasure ∧ Formalism.L2.SG.LocVol.LocTieW X.B.I.cm.sig X.B.I.J ψ v
            (Formalism.L2.SG.TypedSets.frameOf X u) (X.measG.μGv v) μS := fun v =>
      GlobalTheory.T.exists_frameStabilizerHaar_normalised_fibreMeasure X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH hA hC ψ hψ hstd' v D.R.rS
        (Formalism.L2.SG.TypedSets.frameOf X u) T hP (by omega) (X.measG.μGv v) (hG.2.2.2.1 v)
    choose μSv hSv hSt using hS
    have hWn := X.measW_norm u
    obtain ⟨W, hWt, e1, e2, e3, e4, e5⟩ := GlobalTheory.St.MeasWord.exists_measW_prescribed X.B.I.F X.B.I.E X.B.I.cm.sig hCM
      X.B.I.n X.B.I.J hH D.R.rS (Formalism.L2.SG.TypedSets.frameOf X u) T hP
      (X.measW u).μNinf (X.measW u).μHinf μN μH μSv hWn.2.2.2.2.1 hWn.2.1 hN h2 hSv
    refine ⟨W, hWt, e1, e2, ⟨hT1, νH, h1, ?_⟩, ?_, ?_⟩
    · rw [e4]; exact h3
    · rw [e3]; exact hN1
    · intro v; rw [e5]; exact hSt v
  choose mw hw hNinf hHinf hOm hCov hLoc using hW
  let mg : MeasG X.B.I.cm.sig X.B.I.J D.R.rS := { X.measG with μB := μB' }
  have hg : mg.IsTextNorm := ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1, hμB', hG.2.2.2.2.2⟩
  refine ⟨mg, hg, mw, hw, ?_, ψ, hψ, hstd', ?_, ?_⟩
  · refine ⟨hM.1, hM.2.1, hM.2.2.1, fun u => ?_⟩
    have h := hM.2.2.2 u
    constructor
    · show amb (mw u).μNinf = _
      rw [hNinf u]; exact h.1
    · show amb (mw u).μHinf = _
      rw [hHinf u]; exact h.2
  · exact ⟨fun u => ⟨hOm u, hCov u⟩, hBc⟩
  · intro w v
    exact hLoc w v

end GlobalTheory.St.Rescale
end
