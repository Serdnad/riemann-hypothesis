module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle050
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.MeasConjM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle100
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle054
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle049
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXKL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle048
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle021
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.HilbertSchmidtDiagonalInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinGlob
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinJF
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle052

@[expose] public section

section

open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf.NcReal Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj.InfCut
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainStatements.RowRest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem place_eq {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (wf : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0)
    (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ) (Q' : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ)
    (h2 : Q * Q' = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) {t : ℝ} (ht : 0 < t)
    (hc : ∀ a : Fin r, Q *ᵥ Pi.single (eI k r a) 1 = (t : ℂ) ^ (r - (a : ℕ)) • e a ∧
      Q *ᵥ Pi.single (esI k r a) 1 = (star ((t : ℂ) ^ (r - (a : ℕ))))⁻¹ • f a) (κ : ℝ≥0∞) :
    (haarLie (Nset k r) κ).comap (fun γ : Formalism.REAL.UJ ε => (Matrix.of.symm (trG Q Q' γ) : Mt k r)) =
      (κ * ENNReal.ofReal ((t ^ B.kap k r)⁻¹)) • refNg hn ε e f wf (z0v T z) := by
  subst hn
  have hF := JX.isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have emb := embQ hF
  have emb' : MeasurableEmbedding (cM (ε := ε) Q' Q) := cM_measEmb (A' := Q) (B' := Q') h2 h2
  set P := Qm e f wf (z0v T z) with hP
  set P' := Qi ε e f wf (z0v T z) with hP'
  have p1 : P' * P = 1 := Qi_mul_Qm hF
  have p2 : P * P' = 1 := Qm_mul_Qi hF
  have hdi : (P' * Q)⁻¹ = Q' * P := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, h2, Matrix.one_mul, p1]
  have hd : P' * Q ∈ UH (Hpk k r) := by
    show (P' * Q)ᴴ * Hpk k r * (P' * Q) = Hpk k r
    calc _ = Qᴴ * (P'ᴴ * Hpk k r * P') * Q := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [QiHQi hF, hg]
  have hmap := conj_levi hd ht
    (fun a => by
      show (P' * Q) *ᵥ Pi.single _ 1 = _
      rw [← Matrix.mulVec_mulVec, (hc a).1, Matrix.mulVec_smul, ← Qm_e (e := e) (f := f) (wf := wf) (z0 := z0v T z) a,
        Matrix.mulVec_mulVec, p1, Matrix.one_mulVec])
    (fun a => by
      show (P' * Q) *ᵥ Pi.single _ 1 = _
      rw [← Matrix.mulVec_mulVec, (hc a).2, Matrix.mulVec_smul, ← Qm_f (e := e) (f := f) (wf := wf) (z0 := z0v T z) a,
        Matrix.mulVec_mulVec, p1, Matrix.one_mulVec]
      simp)
  have hcomp : cM (ε := ε) P' P = conjM (P' * Q) ∘ cM (ε := ε) Q' Q := by
    funext g
    show P' * uMat g * P = P' * Q * (Q' * uMat g * Q) * (P' * Q)⁻¹
    rw [hdi]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Q' P, h2, Matrix.one_mul, ← Matrix.mul_assoc Q Q', h2, Matrix.one_mul]
  have hu : IsUnit (P' * Q).det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ hd
  have hinj : Function.Injective (conjM (k := k) (r := r) (P' * Q)) := fun x y h => by
    have h' : P' * Q * Matrix.of x * (P' * Q)⁻¹ = P' * Q * Matrix.of y * (P' * Q)⁻¹ := h
    have := congrArg (fun m => (P' * Q)⁻¹ * m * (P' * Q)) h'
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul] at this
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one] at this
    exact this
  have hκ : haarLie (Nset k r) κ = κ • haarLie (Nset k r) 1 := by simp [haarLie]
  ext s hs
  show (haarLie (Nset k r) κ).comap (cM (ε := ε) Q' Q) s =
    ((κ * ENNReal.ofReal ((t ^ B.kap k r)⁻¹)) • (haarLie (Nset k r) 1).comap (cM (ε := ε) P' P)) s
  rw [emb'.comap_apply, Measure.smul_apply, emb.comap_apply, hκ, Measure.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  congr 1
  have h3 := congrArg (fun m : Measure (Mt k r) => m (cM (ε := ε) P' P '' s)) hmap
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  rw [← h3, Measure.map_apply (meas_conjM _) (emb.measurableSet_image.2 hs), hcomp, Set.image_comp,
    Set.preimage_image_eq _ hinj]

theorem pi_smul {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    Measure.pi (fun i => c • μ i) = c ^ Fintype.card ι • Measure.pi μ := by
  lift c to ℝ≥0 using hc
  have : ∀ i, SigmaFinite ((c : ℝ≥0∞) • μ i) := fun i => inferInstanceAs (SigmaFinite (c • μ i))
  refine Measure.pi_eq fun s _ => ?_
  simp [Measure.pi_pi, Finset.prod_mul_distrib]

theorem kap_real (k r : ℕ) :
    (B.kap k r : ℝ) = (4 * (r : ℝ) ^ 3 + 6 * (r : ℝ) ^ 2 + 2 * r) / 3 + k * ((r : ℝ) ^ 2 + r) := by
  have hs : B.kap k r = ∑ j ∈ Finset.range r, 2 * (2 * (j + 1) + k) * (j + 1) := by
    unfold B.kap Mdim
    rw [Fin.sum_univ_eq_sum_range (fun a => 2 * (2 * (r - a) + k + 1 - 1) * (r - a)) r, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.1 hj
    rw [show r - (r - 1 - j) = j + 1 by omega]
    rfl
  rw [hs]
  clear hs
  induction r with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Nat.cast_add, ih]; push_cast; ring

def iF {D : D7} (X : HidaSetting D) : X.B.I.F ≃+* D.host.F :=
  RingEquiv.ofBijective
    ((X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).codRestrict D.host.F (fun a => (X.ιE_F _).2 ⟨a, rfl⟩))
    ⟨fun a b h => by
      have h' := congrArg Subtype.val h
      simp only [RingHom.codRestrict_apply, RingHom.coe_comp, Function.comp_apply] at h'
      exact (algebraMap X.B.I.F X.B.I.E).injective (X.ιE.injective h'),
     fun y => by
      obtain ⟨a, ha⟩ := (X.ιE_F y.1).1 y.2
      exact ⟨a, Subtype.ext ha⟩⟩

theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring_nf

theorem disc_rd (D : D7) (X : HidaSetting D) : |((NumberField.discr X.B.I.F : ℤ) : ℝ)| = D.host.rdE ^ D.R.f := by
  refine Formalism.L2.SG.Pf.Carrier.EnergyMS.discRd_of (fun D X => ?_) finrank_E D X
  have hE : NumberField.discr X.B.I.E = NumberField.discr D.host.E :=
    NumberField.discr_eq_discr_of_ringEquiv X.B.I.E X.ιE
  have hF : NumberField.discr X.B.I.F = NumberField.discr D.host.F :=
    NumberField.discr_eq_discr_of_ringEquiv X.B.I.F (iF X)
  rw [hE, hF, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq]
  push_cast
  rw [abs_pow]

theorem covariance_formula : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula := by
  intro D X Y θ C u hθ
  set ρ : ℝ := 2 * D.host.v with hρ
  have hρ1 : 1 ≤ ρ := Formalism.L2.SG.Pf.LoopBCovN.rdE_ge_one D
  have hρ0 : 0 < ρ := by linarith
  have hrd : D.host.rdE = ρ := by rw [hρ]; unfold Formalism.BasicNotions.Host.v; ring
  have hfr : frS D = ((ρ⁻¹ : ℝ) : ℂ) := by
    unfold frS Formalism.BasicNotions.Host.ka
    congr 1
    have hv : D.host.v ≠ 0 := by intro h; rw [hρ, h] at hρ0; simp at hρ0
    rw [hρ]
    field_simp
  set c : ℝ≥0∞ := Formalism.MainNotions.S.kapN D θ * ENNReal.ofReal (((ρ⁻¹) ^ B.kap D.R.k D.R.rS)⁻¹) with hcdef
  have hloc : ∀ (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F), vOf X τ = v →
      Formalism.L2.SG.Pf.AmpWinLoc.muNl C τ v = c • refNX X u v := by
    rintro τ v rfl
    obtain ⟨-, h2, hg, hcol⟩ := C.isT τ
    rw [hfr] at hcol
    exact place_eq (nX X) _ (eV X _) (ProductExactness.pV X _) (X.wfr u _) (ProductExactness.zV X u _) (ProductExactness.Tw_pos u) (fX_ee X _) (fX_ff X _)
      (fX_ef X _) (fX_ww X u _) (fX_ew X u _) (fX_fw X u _) (fX_ez X u _) (fX_fz X u _) (frame_real_z_z_eq_neg X u _) (fX_zw X u _)
      (C.Q τ) (C.Qi τ) h2 hg (inv_pos.2 hρ0) (fun a => hcol a a rfl) _
  have hv : Formalism.L2.SG.Pf.AmpWinGlob.muNv C = fun v => c • refNX X u v :=
    funext fun v => hloc (X.pl v) v (X.pl.symm_apply_apply v)
  have hsf : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.AmpWinGlob.muNv C v) := fun v => by
    have key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w →
        SigmaFinite (Formalism.L2.SG.Pf.AmpWinLoc.muNl C τ w) := by
      rintro τ w rfl
      exact Formalism.L2.SG.Pf.AmpWinLoc.sf_muNl C τ hθ
    exact key (X.pl v) v (X.pl.symm_apply_apply v)
  have : ∀ v, SigmaFinite (refNX X u v) := fun v =>
    (refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
      (ProductExactness.zV X u v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
      (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (fX_ez X u v)).1
  obtain ⟨hemb, hmapT⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C hsf hθ
  have hcov : Formalism.L2.SG.LoopTerm.dnB D θ (Formalism.L2.SG.LoopTerm.trInf C '' Y.FN u) =
      Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muNv C) (Y.FN u) := by
    rw [← hmapT, hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
  have hce : c = ENNReal.ofReal (ρ ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * ρ ^ (B.kap D.R.k D.R.rS : ℝ)) := by
    rw [hcdef, inv_pow, inv_inv, Real.rpow_natCast, ENNReal.ofReal_mul (by positivity)]
    rfl
  have href := covol_refN (covolN_of_coordCovol (coordCovol_of kapLaw_holds NOf.nofib_holds CovB.blockCovol_holds))
    refNBox_holds X u u (Y.FN u) (Y.FN_fund u)
  have hcard : Fintype.card (InfinitePlace X.B.I.F) = Fintype.card D.what₂.Tau := Fintype.card_congr X.pl
  have hf : D.R.f = Fintype.card D.what₂.Tau := D.what₂.card_Tau.symm
  unfold Formalism.L2.SG.LoopTerm.covN
  rw [hcov, hv, pi_smul _ (by rw [hce]; exact ENNReal.ofReal_ne_top), Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    href, disc_rd D X, hrd, hf, hcard, hce, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
    ← Real.rpow_natCast ρ, ← Real.rpow_mul hρ0.le, mul_comm ((Fintype.card D.what₂.Tau : ℕ) : ℝ), Real.rpow_mul hρ0.le,
    Real.rpow_natCast (ρ ^ Formalism.L2.SG.Pf.LsNc5.covolumeExponent D.R.rS D.R.k), ← mul_pow]
  congr 1
  have e : Formalism.L2.SG.Pf.LoopBCovN.eN D = -((D.R.rS : ℝ) * D.R.k) + (B.kap D.R.k D.R.rS : ℝ) +
      Formalism.L2.SG.Pf.LsNc5.covolumeExponent D.R.rS D.R.k := by
    rw [kap_real]
    unfold Formalism.L2.SG.Pf.LoopBCovN.eN Formalism.L2.SG.Pf.LsNc5.covolumeExponent
    ring
  rw [e, Real.rpow_add hρ0, Real.rpow_add hρ0]
  ring

end Formalism.MainStatements.RowRest
end
end

section

noncomputable section

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.RealObj Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.ThmBChain6

namespace Formalism.MainStatements.RowRest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def UniqOfPin : Prop :=
  ∀ (D : D7), ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))),
    (∀ w, JointQuot.OkPt X u u' w → JointQuot.LocPin X u u' w νl) → LocNorm.LocUniqP u u' C hB νl

def EnergyFin : Prop :=
  ∀ (D : D7), ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u u' : D.what₂.Word), intCe X u u' 1 ≠ ⊤

theorem norm_eq {D : D7} {X : HidaSetting D} {θ : ℝ} (Y : Full X) (C : Choice X θ) (hB : WuBessel C) (hLF : LocFactor C)
    (u u' : D.what₂.Word) (hfin : intCe X u u' 1 ≠ ⊤) {c c' Irat Ire : ℝ}
    (hc : c = (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal / (Module.finrank ℂ (X.Vpi u) : ℝ))
    (hc' : c' = (X.muN u' (Y.FN u')).toReal * (X.muH u' Set.univ).toReal / (Module.finrank ℂ (X.Vpi u') : ℝ))
    (hcc : c * c' ≠ 0) (h1 : (c * c')⁻¹ * IntC X u u' 1 = 2 ^ (D.R.f * (D.R.rS + 1)) * Irat)
    (h2 : Irat = Formalism.FourierDecayAlt.PN.abelian₂ D.host.rdE D.R.rS D.R.k D.R.f *
      D.host.rdE ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3) * Ire)
    {sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hsec : ∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (sec τ)) :
    ∏ τ, MMv D u u' (locS hB u u' τ) (sec τ) =
      ENNReal.ofReal (LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u' * Ire) := by
  have hV := AmpWinJF.levelVolume_pos (X := X)
  have hA : (∏ τ, AmpWin.kap u u' C hB τ) * (c * c') = LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u' := by
    have h := AmpWinGlob.ampWin_of_loc C u Y u' hLF hB
    unfold AmpWin.AmpWinP PoincareInHH.PoincareSetting.c0X at h
    refine mul_left_cancel₀ (pow_pos hV 2).ne' ?_
    rw [← h, hc, hc']
    ring
  have hK : 0 < Kpl D ^ D.R.f := pow_pos (kpl_pos D) _
  have hI : IntC X u u' 1 = c * c' * (Kpl D ^ D.R.f * Ire) := by
    rw [kpl_pow, mul_assoc (2 ^ _), ← h2, ← h1, ← mul_assoc, mul_inv_cancel₀ hcc, one_mul]
  have hE := energy_prod C hB u u' hsec
  have hk0 : 0 ≤ ∏ τ, AmpWin.kap u u' C hB τ := Finset.prod_nonneg fun τ _ => Complex.normSq_nonneg _
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_pow (kpl_pos D).le] at hE
  have e : (∏ τ, AmpWin.kap u u' C hB τ) * (intCe X u u' 1).toReal =
      Kpl D ^ D.R.f * (LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u' * Ire) := by
    rw [← hA]
    show _ * IntC X u u' 1 = _
    rw [hI]; ring
  rw [e, ENNReal.ofReal_mul hK.le] at hE
  exact ((ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 hK).ne' ENNReal.ofReal_ne_top).1 hE).symm

theorem uniform_restriction_of_energy (hF : LoopBCovN.CovNFormula) (hU : UniqOfPin) (hE : EnergyFin) : AmplitudeBoundsAllChoicesUniform := by
  intro Cg cb Cw cT CT C0
  obtain ⟨Cgs, CTs, -, -, a, b, hS⟩ := sizes_of_hypotheses Cg cb Cw cT CT C0
  refine ⟨1, 1, max a 29, max b 16, fun C' Cl h1 h3 D large₂ X Y u u' hc hb X0 ψ _ sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire
    hO ν hp => ?_⟩
  have hG : ConcreteSettingExists.GapHyp D :=
    ThmSOwn.gap_hypothesis_of_hypotheses hc.1.1 (le_trans (le_max_right _ _) h3) (le_trans (le_max_right _ _) h1)
  obtain ⟨-, hb16, hrd0, hrdb, -⟩ := hS C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h3) D large₂ X Y u u' hc
  have hv : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
  obtain ⟨-, -, hNI, -, -, -, hF1, hF2⟩ := hO
  have hP := hNI.1
  set B := bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq with hBdef
  have hc0 : 0 < B.c0 * B.c0' := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p1, p2, p3, p4, -, -, p5, p6, -⟩ := hP
    exact mul_pos (div_pos (mul_pos p3 p1) p5) (div_pos (mul_pos p4 p2) p6)
  have hκ : 0 < MassDataConc.kapN D := by
    have hg : (0 : ℝ) < (Formalism.MainNotions.S.Lat.gS D : ℝ) := by
      have h0 := (D.host.g_prime 0).pos
      have h1 := (D.host.g_prime 1).pos
      unfold Formalism.MainNotions.S.Lat.gS
      positivity
    have := rd_pos D
    unfold MassDataConc.kapN
    positivity
  have hIC : B.IntC = IntC X u u' 1 := by
    show IntC X u u' 1 / MassDataConc.kapN D * kapU D = _
    unfold kapU
    rw [if_pos hκ, div_mul_cancel₀ _ hκ.ne']
  rw [hIC] at hF1
  rw [hv] at hF2 hrdb
  have hrd := rd_pos D
  have hIre : 0 ≤ Ire := by
    have h0 : 0 ≤ (B.c0 * B.c0')⁻¹ * IntC X u u' 1 := mul_nonneg (inv_nonneg.2 hc0.le) ENNReal.toReal_nonneg
    rw [hF1, hF2, ← mul_assoc, ← kpl_pow] at h0
    exact nonneg_of_mul_nonneg_right h0 (pow_pos (kpl_pos D) _) |> fun h => h
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith
  have hrd1 : 1 ≤ D.host.rdE := hv ▸ LoopBCovN.rdE_ge_one D
  have he0 : 0 ≤ LoopBCovN.eN D := by unfold LoopBCovN.eN; positivity
  have hel := LoopBCovN.eN_le D
  refine ⟨hIre, 1, one_pos, LoopBTheta.normWin_one large₂ zero_le_one, fun Cc hB => ?_⟩
  have hLF := LocF.locFactor_holds hG Cc
  obtain ⟨νl, hpin, hQ⟩ := Formalism.L2.S.L6.UnitaryStandardVectors.ooQuot_of_nuQPin X u u' ν hp.2
  have hW : LoopTerm.CovWinN (Y := Y) Cc large₂ 1 u u' := by
    refine LoopBCovN.covWinN_of hF Cc large₂ zero_le_one ?_ u u'
    rw [hv]
    refine mul_le_mul (by nlinarith [sq_nonneg (D.R.m : ℝ)]) (Real.log_le_log hrd hrdb) (Real.log_nonneg hrd1)
      (by positivity)
  obtain ⟨hK0, hK1⟩ := AmpWinGlob.K0_mem_covWin_of_locFactor_wuBessel Cc u Y u' hLF hB (AmpWinJF.levelVolume_pos (X := X))
    (LoopBCovN.covN_pos hF one_pos Cc u u') hW
  refine ⟨⟨νl, hQ, hU D hG X 1 Cc hB u u' νl hpin⟩, hK0, hK1, fun sec hsec => ?_⟩
  rw [norm_eq Y Cc hB hLF u u' (hE D hG X u u') (c := B.c0) (c' := B.c0') rfl rfl hc0.ne' hF1 hF2 hsec]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hIre)
  rw [hF D X Y 1 Cc u one_pos, hF D X Y 1 Cc u' one_pos, one_mul, hv, D.what₂.card_Tau, ← pow_add, ← Real.rpow_natCast,
    ← Real.rpow_mul hrd.le]
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  refine (Real.rpow_le_rpow hrd.le hrdb (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le hb1 ?_)
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hel hf0]

end Formalism.MainStatements.RowRest
end
end
