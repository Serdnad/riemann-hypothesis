module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensitySumsAndDomination
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DFrameAtPfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DFrameAtPfB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle018
public import Formalism.RealPlaceAnalysis.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle002
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

noncomputable section

open scoped InnerProductSpace
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict Formalism.L2.SG.ProjRows Formalism.L2.SG.KerJoinS Formalism.IndefR.Cx Formalism.L2.Indef

namespace Formalism.L2.SG.KerSideCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Chain

theorem chainOpM_add' {Rg : Type} [CommSemiring Rg] {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    {M : ℕ → Type} [∀ j, AddCommMonoid (M j)] [∀ j, Module Rg (M j)]
    (w : ∀ j, ι j → Rg) (Km : ∀ j, ι j → ι (j + 1) → (M j →ₗ[Rg] M (j + 1))) (m : ℕ) (f g : ι 0 → M 0) :
    Formalism.ThetaLiftIndependence.chainOpM w Km m (f + g) = Formalism.ThetaLiftIndependence.chainOpM w Km m f + Formalism.ThetaLiftIndependence.chainOpM w Km m g := by
  induction m with
  | zero => first | rfl | simp [Formalism.ThetaLiftIndependence.chainOpM]
  | succ m ih =>
    simp only [Formalism.ThetaLiftIndependence.chainOpM, ih]
    funext t
    simp [Formalism.ThetaLiftIndependence.kerOpM, Finset.sum_add_distrib, smul_add, map_add (f := _)]

theorem chainOpM_smul' {Rg : Type} [CommSemiring Rg] {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    {M : ℕ → Type} [∀ j, AddCommMonoid (M j)] [∀ j, Module Rg (M j)]
    (w : ∀ j, ι j → Rg) (Km : ∀ j, ι j → ι (j + 1) → (M j →ₗ[Rg] M (j + 1))) (m : ℕ) (c : Rg) (f : ι 0 → M 0) :
    Formalism.ThetaLiftIndependence.chainOpM w Km m (c • f) = c • Formalism.ThetaLiftIndependence.chainOpM w Km m f := by
  induction m with
  | zero => first | rfl | simp [Formalism.ThetaLiftIndependence.chainOpM]
  | succ m ih =>
    simp only [Formalism.ThetaLiftIndependence.chainOpM, ih]
    funext t
    simp [Formalism.ThetaLiftIndependence.kerOpM, Finset.smul_sum, map_smul, smul_smul, mul_comm]

def colL {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) :
    (C.cls 0 → C.Y 0 → ℂ) →ₗ[ℂ] (C.cls R.m → C.Y R.m → ℂ) where
  toFun := C.col
  map_add' f g := chainOpM_add' (ι := C.cls) (M := fun j => C.Y j → ℂ) C.wt C.Kmap R.m f g
  map_smul' c f := chainOpM_smul' (ι := C.cls) (M := fun j => C.Y j → ℂ) C.wt C.Kmap R.m c f

def perColL (D : D7) (u : D.what₂.Word) : D.what₂.Mu u →ₗ[ℂ] D.what₂.Amb D.what₂.mu0 →ₗ[ℂ] ℂ :=
  ((D.mem u).P.period ∘ₗ (D.mem u).P.lowerMap ∘ₗ (D.mem u).P.evz ∘ₗ colL (D.mem u).C ∘ₗ
    (D.mem u).A.Mram.subtype ∘ₗ (D.eMu u).toLinearMap).compl₂ (D.eMt u).symm.toLinearMap

theorem perColL_apply (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) (F : D.what₂.Amb D.what₂.mu0) :
    perColL D u φ F = D.what₂.perCol u D.what₂.mu0 φ F := by
  rw [D.perCol_base_eq_PtilCol]
  simp only [perColL, LinearMap.compl₂_apply, LinearMap.comp_apply, PeriodMap.PtilCol, PeriodMap.Ptil]
  rfl

end Chain

section Read

variable {D : D7} (X : HidaSetting D) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} (Tr : ∀ u, Transport X u (Fm u)) (hK : X.LevelSubgroupCharacter)
  (Dt : D.what₂.Word → Set X.B.I.GA)
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  (P : CxData A) {fc : DefSub A → DefFace Bs}
  (eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH)
  (m : D.what₂.Word → (fc P.zs).Dc.Mem)
  (cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc P.zs).Dc.a (m u)) → ℂ))
  (cF : (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0)
  (eR : D.what₂.EE →ₗ[ℂ] P.EE)

def GoodPartHasComplexCoordinates : Prop := D.what₂.V0 D.what₂.mu0 ≤ LinearMap.range cF

end Read

end Formalism.L2.SG.KerSideCut
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem inv_last {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Z⁻¹ (Fin.last r) (Fin.last r) = Ring.inverse (Formalism.L2.SG.RealObj.Dl Z (r + 1)) * Formalism.L2.SG.RealObj.Dl Z r := by
  have hfull : Formalism.L2.SG.RealObj.Dl Z (r + 1) = Z.det := by
    unfold Formalism.L2.SG.RealObj.Dl; rw [dite_eq_left le_rfl]
    congr 1
  have hr : Formalism.L2.SG.RealObj.Dl Z r = (Z.submatrix (Fin.last r).succAbove (Fin.last r).succAbove).det := by
    unfold Formalism.L2.SG.RealObj.Dl; rw [dite_eq_left (Nat.le_succ r)]
    congr 1; ext i j; simp only [Matrix.submatrix_apply, Fin.succAbove_last]; rfl
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_fin_succ_eq_det_submatrix, hfull, hr]
  have : ((-1 : ℂ) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]; simp
  rw [this, one_mul]

theorem gap_of_G {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hZ : IsUnit Z.det) (T T' : ℝ)
    (hG : 0 < Gv T T' Z) :
    1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))) ≠ 0 := by
  have hfull : Formalism.L2.SG.RealObj.Dl Z (r + 1) = Z.det := by
    unfold Formalism.L2.SG.RealObj.Dl; rw [dite_eq_left le_rfl]
    congr 1
  have hd : Formalism.L2.SG.RealObj.Dl Z (r + 1) ≠ 0 := by rw [hfull]; exact hZ.ne_zero
  rw [inv_last, Ring.inverse_eq_inv']
  set d := Formalism.L2.SG.RealObj.Dl Z (r + 1)
  set e := Formalism.L2.SG.RealObj.Dl Z r
  have hdd : d * starRingEnd ℂ d ≠ 0 := mul_ne_zero hd ((map_ne_zero _).2 hd)
  intro h0
  have h1 : d * starRingEnd ℂ d - (T : ℂ) * T' * (e * starRingEnd ℂ e) = 0 := by
    have e1 : d * starRingEnd ℂ d - (T : ℂ) * T' * (e * starRingEnd ℂ e) =
        (d * starRingEnd ℂ d) * (1 - (T : ℂ) * T' * (d⁻¹ * e * starRingEnd ℂ (d⁻¹ * e))) := by
      have hcd : starRingEnd ℂ d ≠ 0 := (map_ne_zero _).2 hd
      rw [map_mul, map_inv₀]; field_simp
    rw [e1, h0, mul_zero]
  have h2 : ((Complex.normSq d - T * T' * Complex.normSq e : ℝ) : ℂ) = 0 := by
    rw [← h1]; push_cast; rw [Complex.mul_conj, Complex.mul_conj]
  have h3 : Complex.normSq d - T * T' * Complex.normSq e = 0 := by exact_mod_cast h2
  unfold Gv at hG
  rw [Complex.sq_norm, Complex.sq_norm] at hG
  linarith

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.SpectralTiesReal

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

theorem tprod_alpD_pos (D : D7) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) (u u' : D.what₂.Word) :
    0 < ∏' p, alpD u u' p := by
  have hP := Formalism.L2.SG.Pf.placesOver_holds D
  set s := D.R.k - 2 * D.R.rS - 2 with hs
  have hs2 : 2 ≤ s := by omega
  set a : PlF D → ℝ := fun p => (Formalism.L2.SG.DataCut.qP p ^ s)⁻¹ with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => inv_nonneg.2 (pow_nonneg (Formalism.L2.SG.DataCut.qP_nonneg p) _)
  have hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, a p ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    intro S
    exact Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S Formalism.L2.SG.DataCut.qP Loc.resChar D.R.f s hs2
      (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩)
      (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))
  have haS : Summable a := summable_of_sum_le ha0 hsum
  have hαb := Formalism.L2.SG.Pf.alpBound_holds D hk u u'
  have hal0 : ∀ p, 0 < alpD u u' p := fun p => lt_of_lt_of_le (Real.exp_pos _) (hαb p).1
  have hlogα : Summable fun p => Real.log (alpD u u' p) := by
    refine Summable.of_norm_bounded (g := fun p => 2 * a p) (haS.mul_left 2) (fun p => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := Real.log_le_log (Real.exp_pos _) (hαb p).1
    have h2 := Real.log_le_log (hal0 p) (hαb p).2
    rw [Real.log_exp] at h1 h2
    constructor <;> linarith
  rw [← Real.rexp_tsum_eq_tprod hal0 hlogα]
  exact Real.exp_pos _

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
end
end

section

noncomputable section

open NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.PtRepPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace DFrameAtPf

theorem matW_liftU {n k : ℕ} {ε : Fin n → Bool} (wb : Fin k → Fin n → ℂ)
    (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    (Matrix.of fun a b => hJ ε (wb a) (uMat (liftU wb hon U hU) *ᵥ wb b)) = U := by
  ext a b
  rw [Matrix.of_apply, liftU_mulVec]
  have h1 := congrFun (wCoord_liftM hon U (wb b)) a
  have h2 : wCoord ε wb (wb b) = Pi.single b 1 := by
    funext i
    show hJ ε (wb i) (wb b) = _
    rw [hon, Pi.single_apply]
  rw [h2, mulVec_single_one] at h1
  exact h1

end DFrameAtPf

open DFrameAtPf

variable {D : D7}

theorem dFrame_any (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (s0 sc : ℝ) (hsc : sc ≠ 0)
    (i0 : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (γ : X.B.I.Ginf) (hG : ∀ v, 0 < GX X u u' s0 γ v) :
    ∃ h h', IsDFrameX X u u' sc i0 i0 γ h h' := by
  have hloc : ∀ v, ∃ h h' : Matrix (Fin D.R.k) (Fin D.R.k) ℂ,
      IsDFrame (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat (γ v)) (uMat ((γ v)⁻¹)) (X.wfr u v)
        (X.wfr u' v) (i0 v) (i0 v) h h' := fun v =>
    dframe_loc (frU X u v) (frU X u' v) rfl (i0 v) (γ v) sc hsc
      (gv_pos_scale (Tw u) (Tw u') (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u'))
        (uMat (γ v)) s0 sc hsc (hG v))
  choose H H' hH using hloc
  have hon : ∀ uu v, ∀ i j, hJ (X.B.I.ε v) (X.wfr uu v i) (X.wfr uu v j) = if i = j then 1 else 0 :=
    fun uu v => X.wfr_on uu v
  have hmem : ∀ uu (U : ∀ v, Matrix (Fin D.R.k) (Fin D.R.k) ℂ) (hU : ∀ v, U v ∈ Matrix.unitaryGroup _ ℂ),
      (fun v => liftU (X.wfr uu v) (hon uu v) (U v) (hU v) : X.B.I.Ginf) ∈ HsetU X uu := by
    intro uu U hU v x hx
    show uMat (liftU (X.wfr uu v) (hon uu v) (U v) (hU v)) *ᵥ rv X.B.I v x = rv X.B.I v x
    rw [liftU_mulVec]
    refine liftM_fix _ _ fun i => ?_
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
    · exact (frU X uu v).we i a
    · exact (frU X uu v).wf i a
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact (frU X uu v).wz i
  have hmat : ∀ uu (U : ∀ v, Matrix (Fin D.R.k) (Fin D.R.k) ℂ) (hU : ∀ v, U v ∈ Matrix.unitaryGroup _ ℂ) v,
      Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr uu v) v (fun v => liftU (X.wfr uu v) (hon uu v) (U v) (hU v)) = U v :=
    fun uu U hU v => matW_liftU (X.wfr uu v) (hon uu v) (U v) (hU v)
  refine ⟨fun v => liftU (X.wfr u v) (hon u v) (H v) (hH v).1,
    fun v => liftU (X.wfr u' v) (hon u' v) (H' v) (hH v).2.1,
    hmem u H (fun v => (hH v).1), hmem u' H' (fun v => (hH v).2.1), fun v => ?_⟩
  rw [hmat u H (fun v => (hH v).1) v, hmat u' H' (fun v => (hH v).2.1) v]
  exact hH v

theorem dual_frame_at_places (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : DFrameAt X u u' sc i0 i0 := by
  intro hsc w _ hG
  exact dFrame_any X u u' D.host.rdE sc hsc.ne' i0 (gamW X u u' w) hG

end Formalism.L2.SG.Pf.Carrier
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyPlace

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def lamA (P : Parts X u u') (a : Fin P.S.G.r) : ℝ := ((P.S.g : ℝ) / (2 * Real.pi)) ^ (2 * (P.S.G.r - a.val))

def phiQ (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (cv : Fin (D.R.rS + 1) → ℂ) : (Fin P.S.G.r → ℂ) × ℂ :=
  (fun a => ((lamA P a : ℝ) : ℂ) * cv ⟨a.val, by have := a.2; omega⟩, cv ⟨D.R.rS, by omega⟩)

def K0 (P : Parts X u u') : ℝ :=
  2 ^ (P.S.G.r + 1) * ∏ a : Fin P.S.G.r, (lamA P a ^ (2 * (Formalism.QuantumDeterminants.Mdim P.S.G.k P.S.G.r a - 1)))⁻¹

def PlaceNorm (P : Parts X u u') (hr : P.S.G.r = D.R.rS)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) : Prop :=
  ∀ v, ∀ cv ∈ GoodV u u', L v cv =
    ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
      (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base (phiQ P hr cv)))‖ ^ 2

def ChangeVar (P : Parts X u u') (hr : P.S.G.r = D.R.rS) : Prop :=
  P.S.G.k = D.R.k →
    (∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u') →
    ∀ v (F : (Fin P.S.G.r → ℂ) × ℂ → ℝ), (∀ q, 0 ≤ F q) →
      ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * F (phiQ P hr cv)) ∂(dcV (D := D)) =
        ENNReal.ofReal (K0 P) * ∫⁻ q, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight P.S.G.k P.S.G.r
          (Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z)
          (Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z') q * F q)

def KMatch (P : Parts X u u') : Prop :=
  (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) → Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE → P.S.G.r = D.R.rS →
    P.S.G.k = D.R.k → 0 < P.S.g → 1 ≤ P.S.G.k → K0 P = EnergyConst.Kexp P

end Formalism.L2.SG.Pf.Carrier.EnergyPlace
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.EnergyConst2

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf Formalism.L2.SG.Pf.Carrier.EnergyConst

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}


variable (X u u') in
def LemmaMSStd (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : Prop :=
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ → Formalism.L2.SG.LocVol.IsStdChar ψ → Formalism.L2.SG.LocVol.ProdConv X u u' ψ →
    LemmaMS X u u' ψ

end Formalism.L2.SG.Pf.Carrier.EnergyConst2
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

section Pack

variable {n : ℕ} (ε : Fin n → Bool)

def mkUJ (y : Matrix (Fin n) (Fin n) ℂ) (hy : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨y, Formalism.REAL.Jm ε * yᴴ * Formalism.REAL.Jm ε,
    mul_eq_one_comm.1 (by
      calc Formalism.REAL.Jm ε * yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε * (yᴴ * Formalism.REAL.Jm ε * y) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hy, Formalism.REAL.Jm_mul_self]),
    by
      calc Formalism.REAL.Jm ε * yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε * (yᴴ * Formalism.REAL.Jm ε * y) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hy, Formalism.REAL.Jm_mul_self]⟩, hy⟩

end Pack

section Adj

variable {m : ℕ}

end Adj

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end
