module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.AmpTensorDSdNonemptyOfSubsingleton
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
public import Formalism.SharpRestriction.CuspSpanNormBounds.BigCellDensity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.RStabInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.AmpWinRX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF)) {θ : ℝ} (C : Choice X θ)
  (u u' : D.what₂.Word)

theorem goodW_all (τ : D.what₂.Tau) : GoodW D τ u u' θ (locW C u u' τ) :=
  goodW_of C u u' τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u' τ) (Formalism.L2.SG.Pf.zTr C u τ)
    (Formalism.L2.SG.Pf.zTr C u' τ) (Formalism.L2.SG.Pf.haarTr C τ)

end Formalism.L2.SG.Pf.AmpWinRX
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.GoodS

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem v0_ne (C : Choice X θ) (τ : D.what₂.Tau) : v0Of C τ ≠ 0 := by
  intro h0
  have hy : (C.Q τ * C.y τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.y τ * C.Qi τ) =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    have hg := (C.isT τ).2.2.1
    have hyU : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
    calc (C.Q τ * C.y τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.y τ * C.Qi τ)
        = (C.Qi τ)ᴴ * ((C.y τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.y τ) * C.Qi τ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [hg, hyU, qiHqi _ (C.isT τ).2.1 hg]
  have hn := (X.ds (vOf X τ)).2.2.1.2.1 _ hy (X.B.w (vOf X τ))
  have h1 := (X.low (vOf X τ)).1
  unfold v0Of sigB at h0
  rw [h0, norm_zero] at hn
  rw [← hn] at h1
  exact zero_ne_one h1

theorem finrank_pos (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : 0 < Module.finrank ℂ (X.Vloc u v) := by
  have : Nontrivial (X.Vloc u v) := (X.piLoc_type u v).1
  exact Module.finrank_pos

theorem l2SG_const_smul {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (s : ℂ) (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) :
    l2SG ν (fun m => s • f m) = (‖s‖₊ : ℝ≥0∞) ^ 2 * l2SG ν f := by
  unfold l2SG
  simp only [nnnorm_smul, ENNReal.coe_mul, mul_pow]
  first
    | exact lintegral_const_mul' _ _ (by simp)
    | exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)

theorem goodSRest_of {C : Choice X θ} (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hsm : v0Of C τ ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ))
    (hLu : l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 ∧ l2SG (C.nuS u τ) (phiOf hB u τ) < ⊤)
    (hLu' : l2SG (C.nuS u' τ) (phiOf hB u' τ) ≠ 0 ∧ l2SG (C.nuS u' τ) (phiOf hB u' τ) < ⊤)
    (hT : Formalism.BasicNotions.dsigTie D) : GoodSRest hB u u' τ := by
  set v := vOf X τ
  have hd : (0 : ℝ) < Module.finrank ℂ (X.Vloc u v) := by exact_mod_cast finrank_pos u v
  have hd' : (0 : ℝ) < Module.finrank ℂ (X.Vloc u' v) := by exact_mod_cast finrank_pos u' v
  have hL : 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal := ENNReal.toReal_pos hLu.1 hLu.2.ne
  have hL' : 0 < (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal := ENNReal.toReal_pos hLu'.1 hLu'.2.ne
  have hc : 0 < cOf hB u τ := div_pos hL hd
  refine ⟨Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ, Formalism.L2.SG.Pf.dsTr C τ, hsm, v0_ne C τ, hc, ?_, ?_, ?_⟩
  · show l2SG (C.nuS u τ) (phiOf hB u τ) = _
    rw [cOf, div_mul_cancel₀ _ hd.ne', ENNReal.ofReal_toReal hLu.2.ne]
  · show l2SG (C.nuS u' τ) (fun m => sclOf hB u u' τ • phiOf hB u' τ m) = _
    rw [l2SG_const_smul, sclOf]
    set a := cOf hB u τ * (Module.finrank ℂ (X.Vloc u' v) : ℝ) / (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal
      with ha
    have ha0 : 0 ≤ a := div_nonneg (mul_nonneg hc.le hd'.le) hL'.le
    have hnorm : (‖((Real.sqrt a : ℝ) : ℂ)‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal a := by
      rw [← enorm_eq_nnnorm, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt ha0]
    rw [hnorm, ← ENNReal.ofReal_toReal hLu'.2.ne, ← ENNReal.ofReal_mul ha0, ha, div_mul_cancel₀ _ hL'.ne']
  · obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
    refine ⟨P, hP.1, ?_⟩
    have hε : ∀ i, epsSH D.R i = X.B.I.ε v (Fin.cast (n_eq' X).symm i) := fun i => by
      rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl)
    have hF := fdegHpk_tr (n_eq' X) (X.B.I.ε v) (epsSH D.R) hε (X.B.σ v) (X.ds v).2.2.1
      (Formalism.L2.SG.Pf.RowDictPf.fdeg_of_schur X Formalism.L2.SG.Pf.RowDictPf.schur_orthogonality_discrete_series v)
      (C.Q τ) (C.Qi τ) (C.isT τ).2.1 (C.isT τ).2.2.1 P hP
    have hDS := dsHpk_tr (n_eq' X) (X.B.I.ε v) (epsSH D.R) hε (X.B.lam v) (lamSH D.R (D.hc τ))
      (fun i => by
        rw [X.lam_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
        exact congrArg (lamS D.R (D.hc τ)) (Fin.ext rfl))
      (X.B.σ v) (X.ds v) (C.Q τ) (C.Qi τ) (C.isT τ).2.1 (C.isT τ).2.2.1 P hP
    have hF2 := Formalism.L2.SG.Pf.RowDictPf.isFdeg_smul (D.s.cdScale_pos _ (epsSH D.R)) hF
    have htie := hT τ (X.B.H v) _ _ hDS hF2
    rw [← htie]
    exact hF2

end Formalism.L2.SG.Pf.GoodS
end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.BigCellDensity
open scoped ComplexConjugate

namespace Formalism.L2.SG.Pf.RootHaarLoc

section rootG

variable {k0 r : ℕ} (zz : Fin (2 * r + (k0 + 1) + 1) → ℂ) {Wp' Wq' : Type} [NormedAddCommGroup Wp']
  [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq']
  (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r Wp' Wq') (hz : Ds.z = zz) (γ : Point ℂ (r + 1))
  {g : Formalism.FourierDecayAlt.B.Mat (k0 + 1) r} (hg : g ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r) {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Formalism.QuantumDeterminants.Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) d)
include hz hg hd hZ

theorem rootCoords_psiG (y : (rootPat γ) → ℂ) :
    rootCoords (k0 + 1) r zz γ (Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ y))) = y := by
  have hG := good_of Ds hg hd hZ
  have hs := (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_spec Ds hg hd hG (Tinv γ y)).2
  funext p
  have hp := p.2
  simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have ha : p.1.1.val < r := by
    have h1 := p.1.2.isLt
    have h2 := Fin.lt_def.1 hp.1
    omega
  simp only [rootCoords, Equiv.apply_symm_apply]
  rw [flag_eq_uMap _ _ _ _ _ _ ha, ← hz, hs, Matrix.conjTranspose_apply]
  have hc := Formalism.FourierDecayAlt.P.Dx2.Rad.low_coord (wPt γ) (Tinv γ y) (eRoot γ p)
  simp only [eRoot, Equiv.coe_fn_mk] at hc
  rw [hc]
  simp [Tinv, eRoot]

theorem psi_rootCoordsG (x : Mt (k0 + 1) r) (hx : Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset g) :
    Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ (rootCoords (k0 + 1) r zz γ x))) = x := by
  have hG := good_of Ds hg hd hZ
  have hu := Formalism.FourierDecayAlt.P.Dx2.Rad.u_eq_low Ds hg hd hG (ρ := Matrix.of x) hx
  have hphi : Formalism.FourierDecayAlt.P.Dx2.Rad.phi0 Ds (wPt γ) (Matrix.of.symm (Matrix.of x)) =
      Tinv γ (rootCoords (k0 + 1) r zz γ x) := by
    funext q
    have hb : q.1.2.val < r := by
      have h1 := q.1.1.isLt
      have h2 := Fin.lt_def.1 q.2.1
      omega
    simp only [Formalism.FourierDecayAlt.P.Dx2.Rad.phi0, Tinv, rootCoords, Equiv.apply_symm_apply, eRoot, Equiv.coe_fn_symm_mk]
    rw [flag_eq_uMap _ _ _ _ _ _ hb, hz]
  have hρ := Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_unique Ds hg hd hG (Tinv γ (rootCoords (k0 + 1) r zz γ x)) hx
    (by rw [← hphi, ← hu, Matrix.conjTranspose_conjTranspose])
  rw [← hρ]
  rfl

theorem muR_map_rootG :
    (Formalism.FourierDecayAlt.D.muR Ds g (wPt γ)).map (rootCoords (k0 + 1) r zz γ) = volume := by
  have hG := good_of Ds hg hd hZ
  have hm := Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_meas Ds hg hd hG
  show (volume.map fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)).map _ = _
  rw [Measure.map_map (meas_rootCoords _ γ) hm]
  have e : (rootCoords (k0 + 1) r zz γ ∘ fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)) = Tmap γ := by
    funext x
    have := rootCoords_psiG zz Ds hz γ hg hd hZ (Tmap γ x)
    rw [Tinv_Tmap] at this
    exact this
  rw [e]
  exact (Tmap_mp γ).map_eq

end rootG

theorem zhat_inv {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) (hu : IsUnit g.det) (i a : Fin (r + 1)) :
    Formalism.QuantumDeterminants.Zhat k r z' z g⁻¹ i a = star (Zhat k r z z' g a i) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.conjTranspose_apply, Hpk, Fin.mk.injEq]
    split_ifs <;> first | (simp; done) | omega
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hu
  have hkey : (Hpk k r * g)ᴴ = Hpk k r * g⁻¹ := by
    rw [Matrix.conjTranspose_mul, hH]
    have h2 := congrArg (· * g⁻¹) hg'
    simp only [Matrix.mul_assoc, hgi, Matrix.mul_one] at h2
    exact h2
  unfold Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hkey]
  generalize Hpk k r * g = M
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.star_dotProduct_star, star_star]

theorem locRootHaar (k r : ℕ) (hk : 1 ≤ k) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hg : g₀ ∈ UH (Hpk k r)) (hZ : Formalism.MainNotions.S.ZhatO k r z z' g₀ = ptMat p) :
    ∃ (μ₀ : Measure (Mt k r)) (c : ENNReal), Formalism.MainNotions.S.IsHaarOn (Formalism.MainNotions.S.Rset k r g₀) μ₀ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
      μ₀.map (rootCoords k r z' p) = c • volume := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  obtain ⟨Ds, hDz, hDz'⟩ := Formalism.MainNotions.S.Pv.AmpDDPf.bsetting_of (k0 + 1) r hk z' z ⟨hz', hT'⟩ ⟨hz, hT⟩
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed (k0 + 1) r
  have hgG : g₀ ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r := hg
  have hu : IsUnit g₀.det := hG.unit g₀ hgG
  have hgi : g₀⁻¹ ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r := hG.inv_mem g₀ hgG
  set w := wPt p with hw
  let d : Fin (r + 1) → ℂ := fun a => (-1 : ℂ) ^ (r - (w a).val) * star (dPt p (w a))
  have hd : ∀ a, d a ≠ 0 := fun a => mul_ne_zero (pow_ne_zero _ (by norm_num)) (star_ne_zero.2 (dPt_ne p (w a)))
  have hmono : ptMat p = Formalism.FourierDecayAlt.C2.monoP w (dPt p) := by rw [← ptMatN_swap, ptMatN_mono]
  have hZ' : Formalism.QuantumDeterminants.Zhat (k0 + 1) r Ds.z Ds.z' g₀⁻¹ = Formalism.FourierDecayAlt.C2.monoP w d := by
    ext i a
    rw [hDz, hDz', zhat_inv z z' hg hu i a]
    have h1 := congrFun (congrFun hZ a) i
    unfold Formalism.MainNotions.S.ZhatO at h1
    have hs : ((-1 : ℂ) ^ (r - i.val)) * (-1 : ℂ) ^ (r - i.val) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have h2 : Formalism.QuantumDeterminants.Zhat (k0 + 1) r z z' g₀ a i = (-1 : ℂ) ^ (r - i.val) * ptMat p a i := by
      rw [← h1, ← mul_assoc, hs, one_mul]
    rw [h2, hmono]
    simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply]
    by_cases hai : a = w i
    · have hia : i = w a := by rw [hai, wPt_invol]
      rw [if_pos hai, if_pos hia]
      simp only [d, star_mul', star_pow, star_neg, star_one]
      rw [← hia]
    · have hia : ¬ i = w a := fun h => hai (by rw [h, wPt_invol])
      rw [if_neg hai, if_neg hia, mul_zero, star_zero]
  have hH := Formalism.FourierDecayAlt.P.radial_measure_is_haar (k0 + 1) r ℂ ℂ Ds g₀⁻¹ w d hgi hd hZ'
  have hset : Formalism.FourierDecayAlt.C6.Rset g₀⁻¹ = Formalism.MainNotions.S.Rset (k0 + 1) r g₀ := by
    ext x
    simp only [Formalism.FourierDecayAlt.C6.Rset, Formalism.MainNotions.S.Rset, Set.mem_setOf_eq, Matrix.nonsing_inv_nonsing_inv _ hu]
  refine ⟨Formalism.FourierDecayAlt.D.muR Ds g₀⁻¹ w, 1, ⟨Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hH, hH.ne_zero, ?_, ?_⟩, one_ne_zero,
    ENNReal.one_ne_top, ?_⟩
  · rw [← hset]; exact hH.conc
  · intro s hs; rw [← hset] at hs; exact hH.left s hs
  · rw [one_smul]
    exact muR_map_rootG z' Ds hDz p hgi hd hZ'

end Formalism.L2.SG.Pf.RootHaarLoc
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.BigCellDensity
open scoped InnerProductSpace

def TopLevelBesselHypothesis : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq)
    (ν' : Fin (2 * r + (k0 + 1) + 1) → ℂ) (m₀ : Formalism.FourierDecayAlt.B.Mat (k0 + 1) r),
    L.c = cStd → 0 < L.κN → L.κN ≠ ⊤ → Ds.z = L.z → Ds.z' = L.z' → Ds.π = L.π → Ds.π' = L.π' →
    Ds.μW = L.μW → Ds.μN = L.μN → Ds.μW' = L.μW' → Formalism.FourierDecayAlt.D.IsBaseFrame Ds ν' m₀ →
      ∀ (F : ThB.Mx (k0 + 1) r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)), IsKFinCoefH L.σ F →
        Formalism.FourierDecayAlt.B.InCC (A0 (k0 + 1) r) 1 F →
        0 < ThB.Gpt (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') γ → (∃ g, IsPtRep L γ g ∧ IsRelStab L g) →
        ThB.orbSq L F γ = ENNReal.ofReal (Real.pi ^ (2 * pc r (γ.1.map Prod.snd)) *
          (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))
            (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))).re)

theorem topLevelBesselHypothesis : TopLevelBesselHypothesis := by
  have hDF := Formalism.FourierDecayAlt.P.exists_isotropic_frame
  have hVI := Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep
  have hPR := Formalism.FourierDecayAlt.P.relevant_points_holds
  have hRM := root_measure_of_mu_R
  have hQE := quotient_exists
  have hCut := K_finite_decay
  have hRI := repIndep_of K_finite_decay orbital_norm_independence
  intro k0 r L Ds ν' m₀ hc hκ0' hκ1 hz hz' hπ hπ' hW hN hW' hBF
  have hκ0 : L.κN ≠ 0 := hκ0'.ne'
  intro F γ hK hdec hpos _
  have hp : Formalism.FourierDecayAlt.D.IsLocPt (γ.1.map Prod.swap) (r + 1) := isLocPt_swap γ
  have hG : 0 < Formalism.FourierDecayAlt.D.ptG (Tz (k0 + 1) r Ds.z * Tz (k0 + 1) r Ds.z') r (γ.1.map Prod.swap) := by
    rw [ptG_eq_GPoint, hz, hz']
    exact hpos
  obtain ⟨g, hgG, hgZ, hgF⟩ := hDF (k0 + 1) r L.Wp L.Wq Ds ν' m₀ _ hBF hp hG
  have hvec := hVI (k0 + 1) r L.Wp L.Wq Ds ν' m₀ F _ hp g hBF hG hgG hgZ hgF
  have hrep : IsPtRep L γ g := ⟨hgG, by rw [← hz, ← hz', hgZ, ptMatN_swap]⟩
  have hrelD := hPR (k0 + 1) r L.Wp L.Wq Ds _ g hp hgG hgZ
  have hrel : IsRelStab L g := fun a ha => by
    have h1 := hrelD.2 a ha
    rw [hz, hz'] at h1
    rw [hc]
    exact h1
  have hroot := hRM k0 r L Ds γ g hp hc hz hz' hgG hgZ
  obtain ⟨ν, hq⟩ := hQE k0 r L γ g _ hc hκ0 hκ1 hrep hrel hroot
  have hcard_pos : (0 : ℝ) < Real.pi⁻¹ ^ (rootPat γ).card := by positivity
  have hl0 : ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hcard_pos
  have hq' := isOrbQuot_rescale L _ ENNReal.ofReal_ne_top hq
  have hconc : Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap))
      {x | Matrix.of x ∉ RStab (k0 + 1) r g} = 0 := by
    have h1 := hroot.1
    rw [Measure.smul_apply, smul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hl0
    · exact h
  have hne : Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap)) ≠ 0 := by
    intro h0
    apply muR_ne_zero L hc γ g _ hroot
    rw [h0, smul_zero]
  have : SFinite (Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap))) := by
    unfold Formalism.FourierDecayAlt.D.muR
    infer_instance
  have hcut := hCut k0 r L Ds γ g hp F hc hz hz' hπ hπ' hW hN hW' hK hdec hpos hgG hgZ
  have hJ := orbJ_eq L Ds hc hκ0 hκ1 hz hz' hπ hπ' hW hN hW' hgG hrel hconc hne hq' F hcut
  have hsm : OrbInt L F g (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • ν) =
      (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card)).toReal • OrbInt L F g ν := by
    unfold OrbInt
    rw [integral_smul_measure]
  rw [hvec, hJ, hsm,
    orbSq_eq_of L F γ (hsNormSq (OrbInt L F g ν))
      (fun g' μ' ν' h' => hRI k0 r L Ds F γ hc hκ0 hκ1 hz hz' hπ hπ' hW hN hW' hK hdec hpos g' μ' ν' g _ ν h' ⟨hrep, hrel, hroot, hq⟩)
      ⟨g, _, ν, hrep, hrel, hroot, hq⟩]
  congr 1
  rw [show (Formalism.FourierDecayAlt.B.hsInner ((ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card)).toReal • OrbInt L F g ν)
      ((ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card)).toReal • OrbInt L F g ν)).re =
      hsNormSq ((ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card)).toReal • OrbInt L F g ν) by rw [hsNormSq, hsInner_eq],
    Formalism.MainNotions.BigCellDensity.hsNormSq_smul, ENNReal.toReal_ofReal hcard_pos.le]
  rw [← card_rootPat γ]
  have h1 : Real.pi ^ (2 * (rootPat γ).card) * (Real.pi⁻¹ ^ (rootPat γ).card) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm (rootPat γ).card 2, ← mul_pow, mul_inv_cancel₀ Real.pi_ne_zero, one_pow]
  rw [← mul_assoc, h1, one_mul]

end Formalism.L2.SG.Pf.BesselExpansion
end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.monomialWeightModel

open Formalism.MainNotions.BigCellDensity Formalism.FourierDecayAlt.P.Dx2.Rad

variable {r : ℕ} (pN : Formalism.MainNotions.S.Point ℂ (r + 1))

local notation "W" => wPt pN

theorem w_symm (x : Fin (r + 1)) : (W).symm x = W x := wPt_symm pN x

def sw (q : Formalism.FourierDecayAlt.C2.Lstidx W) : Formalism.FourierDecayAlt.C2.Lstidx W :=
  ⟨(W q.1.2, W q.1.1), by
    exact ⟨by simpa only [w_symm] using q.2.2,
      by simpa only [w_symm, wPt_invol] using q.2.1⟩⟩

variable (d : Fin (r + 1) → ℂ)

def Rm (x' : Formalism.FourierDecayAlt.C2.Lstidx W → ℂ) : Formalism.FourierDecayAlt.C2.Lstidx W → ℂ :=
  fun q => d (W q.1.1) / d (W q.1.2) * star (x' (sw pN q))

private theorem low_apply' (v : Formalism.FourierDecayAlt.C2.Lstidx W → ℂ) (i j : Fin (r + 1)) :
    low W v i j = (if i = j then 1 else 0) +
      (if h : j < i ∧ (W).symm i < (W).symm j then v ⟨(i, j), h⟩ else 0) := by
  simp only [Formalism.FourierDecayAlt.P.Dx2.Rad.low, Formalism.FourierDecayAlt.C2.lowOf, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  congr 1
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro q _ hq
      rw [ite_eq_right]
      intro hq'
      exact hq (Subtype.ext hq')
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  · refine Finset.sum_eq_zero fun q _ => ?_
    rw [ite_eq_right]
    intro hq'
    apply h
    have hq2 := q.2
    rw [hq'] at hq2
    exact hq2

theorem low_R_mono (hd : ∀ a, d a ≠ 0) (x' : Formalism.FourierDecayAlt.C2.Lstidx W → ℂ) :
    low W (Rm pN d x') * Formalism.FourierDecayAlt.C2.monoP W d = Formalism.FourierDecayAlt.C2.monoP W d * (low W x')ᴴ := by
  ext i b
  rw [Matrix.mul_apply, Matrix.mul_apply,
    Finset.sum_eq_single ((wPt pN) b) (fun c _ hc => by simp [Formalism.FourierDecayAlt.C2.monoP, hc]) (by simp),
    Finset.sum_eq_single ((wPt pN) i) (fun a _ ha => by
      have hia : i ≠ (wPt pN) a := fun hi => ha (by rw [hi, wPt_invol])
      simp [Formalism.FourierDecayAlt.C2.monoP, hia]) (by simp)]
  simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply, Matrix.conjTranspose_apply,
    wPt_invol, ite_true]
  rw [low_apply', low_apply']
  by_cases h1 : i = (wPt pN) b
  · subst h1
    simp [wPt_invol, w_symm]
  · have h1' : b ≠ (wPt pN) i := fun h => h1 (by rw [h, wPt_invol])
    rw [ite_eq_right h1, ite_eq_right h1', zero_add, zero_add]
    have key : ((wPt pN) b < i ∧ (wPt pN).symm i < (wPt pN).symm ((wPt pN) b)) ↔
        ((wPt pN) i < b ∧ (wPt pN).symm b < (wPt pN).symm ((wPt pN) i)) := by
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, w_symm, w_symm]
      exact And.comm
    by_cases h2 : (wPt pN) b < i ∧ (wPt pN).symm i < (wPt pN).symm ((wPt pN) b)
    · have h3 := key.1 h2
      have hsw : sw pN ⟨(i, (wPt pN) b), h2⟩ = ⟨(b, (wPt pN) i), h3⟩ :=
        Subtype.ext (Prod.ext (wPt_invol pN b) rfl)
      rw [dite_eq_left h2, dite_eq_left h3]
      simp only [Rm]
      rw [hsw, wPt_invol]
      field_simp [hd b]
    · have h3 : ¬ ((wPt pN) i < b ∧ (wPt pN).symm b < (wPt pN).symm ((wPt pN) i)) := fun h => h2 (key.2 h)
      rw [dite_eq_right h2, dite_eq_right h3]
      simp

theorem mono_mul_inv (hd : ∀ a, d a ≠ 0) :
    Formalism.FourierDecayAlt.C2.monoP W d * Formalism.FourierDecayAlt.C2.monoP (wPt pN).symm (fun j => (d ((wPt pN).symm j))⁻¹) = 1 := by
  ext i b
  simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single ((wPt pN).symm b)]
  · simp only [Equiv.apply_symm_apply, ite_true]
    split_ifs with h
    · exact mul_inv_cancel₀ (hd _)
    · exact zero_mul _
  · intro a _ ha
    simp [ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Formalism.L2.SG.monomialWeightModel

end
end
