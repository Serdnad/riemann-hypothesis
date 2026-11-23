module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeSS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OoConvOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiRegOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuadAOf
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutIntervalLong
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle015
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle055
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle150
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolPh
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle152
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle154
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle153
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle140
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle110
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle131
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle057
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFSS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle159
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtOfAdmissibleList

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem quadConv_of (hSch : SchurH) (hNIs : NormIdSm) (hNI : NormInv) (hGS : GrowthS) (hGG : GrowthG)
    (hDD : DecDD) (hBC : BeConv) : More.QuadConv := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS1 hS2 l l' hbe hbe'
  exact ⟨fun γ hγ => quadA_of hSch hNIs hNI hGG hDD hBC hIn D hS1 hS2 hbe hbe' hγ,
    quadB_of hNI hGS hGG hDD hIn D hS1 hbe⟩

end Formalism.FourierDecayAlt.P.S3dx4

theorem Formalism.FourierDecayAlt.P.regularity_bundle_from_hypotheses : Formalism.FourierDecayAlt.ThreeDimData.More.MoreOfSteps :=
  fun hSch hNIs hNI hGS hGG hDD hBC _ =>
    ⟨Formalism.FourierDecayAlt.P.S3dx4.phiReg_of hSch hNIs hGG hDD hBC, Formalism.FourierDecayAlt.P.S3dx4.ooConv_of hSch hNIs hNI hGG hDD hBC,
      Formalism.FourierDecayAlt.P.S3dx4.quadConv_of hSch hNIs hNI hGS hGG hDD hBC⟩
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

variable {k r : ℕ}

def qOf (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : (Fin r → ℂ) × ℂ :=
  (fun a => Formalism.QuantumDeterminants.cmin k r z z' g a, Formalism.QuantumDeterminants.zeta k r z z' g)

theorem qOf_contOn (z z' : Fin (2 * r + k + 1) → ℂ) : ContinuousOn (qOf z z') (Q.OmPlus k r z z') := by
  refine ContinuousOn.prodMk ?_ ?_
  · refine continuousOn_pi.2 fun a => ?_
    show ContinuousOn (fun g : B.Mat k r => Dmin k r z z' g ⟨a.val + 1, by omega⟩ / Dmin k r z z' g ⟨a.val, by omega⟩) _
    exact (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn.div (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn
      fun g hg => hg.1 ⟨a.val, by omega⟩ (by simp)
  · show ContinuousOn (fun g : B.Mat k r => Dmin k r z z' g (Fin.last (r + 1)) / Dmin k r z z' g ⟨r, by omega⟩) _
    exact (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn.div (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn
      fun g hg => hg.1 ⟨r, by omega⟩ le_rfl

theorem isOpen_qOf (z z' : Fin (2 * r + k + 1) → ℂ) {U : Set ((Fin r → ℂ) × ℂ)} (hU : IsOpen U) :
    IsOpen (Q.OmPlus k r z z' ∩ qOf z z' ⁻¹' U) :=
  (qOf_contOn z z').isOpen_inter_preimage (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open z z') hU

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem qOf_sgs (Bs : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : Bs.inSS p) (g : B.Mat k r) :
    qOf Bs.z Bs.z' (B.sgs p g) = qOf Bs.z Bs.z' g := by
  unfold qOf Formalism.QuantumDeterminants.cmin Formalism.QuantumDeterminants.zeta
  simp only [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]

theorem qOf_gq (Bs : B.RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ JF.QDom k r Bs.z Bs.z') :
    qOf Bs.z Bs.z' (B.gq Bs q) = q :=
  Prod.ext (funext fun a => Formalism.FourierDecayAlt.P.BigCellZetaMinors.cmin_gq Bs hq a) (Formalism.FourierDecayAlt.P.BigCellZetaMinors.zeta_gq Bs hq)

theorem om_eq_sgs (Bs : B.RealPlaceData k r Wp Wq) {g : B.Mat k r} (hg : g ∈ JF.Om k r Bs.z Bs.z') :
    ∃ p, Bs.inSS p ∧ qOf Bs.z Bs.z' g ∈ JF.QDom k r Bs.z Bs.z' ∧ g = B.sgs p (B.gq Bs (qOf Bs.z Bs.z' g)) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := Formalism.FourierDecayAlt.P.psiOnto_true k r Wp Wq Bs g hg
  rw [qOf_sgs Bs hp, qOf_gq Bs hq]
  exact ⟨p, hp, hq, rfl⟩

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem agree_qOf (Bs : B.RealPlaceData k r Wp Wq) (J F : B.Mat k r → (Wq →L[ℂ] Wp)) (U : Set ((Fin r → ℂ) × ℂ))
    (hJ : J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0})
    (hag : ∀ q ∈ JF.QDom k r Bs.z Bs.z', q ∈ U → J (B.gq Bs q) = B.JF Bs F (B.gq Bs q)) :
    ∀ g ∈ JF.Om k r Bs.z Bs.z', qOf Bs.z Bs.z' g ∈ U → J g = B.JF Bs F g := by
  intro g hg hgU
  obtain ⟨p, hp, hq, hge⟩ := om_eq_sgs Bs hg
  set q := qOf Bs.z Bs.z' g with hqdef
  rw [hge]
  have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom Bs hq
  have hD : ∀ y ∈ JF.Om k r Bs.z Bs.z', y ∈ Q.Glev k r 0 ∩ {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := fun y hy =>
    ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hy.1, Formalism.FourierDecayAlt.P.CutMP.jdc_of_om _ _ hy⟩
  have hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, n ∈ Q.Nlev k r 0 := fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Bs.z Bs.z' cStd Bs.π Bs.π' Bs.μW Bs.μN Bs.μW' F Bs.z_mem Bs.z'_mem
    Bs.haarN.conc (fun n₀ h => Bs.haarN.left n₀ h)
  refine LT.agree_sgs Bs J (B.JF Bs F)
    (fun y hy n hn => hJ.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hJ.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hJ.2.2.2 y (hD y hy) h hh h' hh')
    (fun y _ n hn => ?_) (fun y _ n hn => ?_)
    (fun y _ h hh h' hh' => Formalism.FourierDecayAlt.P5.jf_uEquiv Bs F y hh hh')
    hp hgq (hag q hq hgU)
  · have e := hN y n hn 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z'_mem, mul_one] at e
    exact e
  · have e := hN y 1 WeylGroupFacts.mem_n_one n hn
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z_mem, one_mul] at e
    exact e

end Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO

end
end

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section wave

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def Xw (S : C.HidaSetting E Wp Wq) (i : ℕ) (v : Fin S.f) : ℝ :=
  (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r i 0)) * Real.exp 1 * (28 * S.G.N / S.G.lenI) ^ (2 * (i - 1) + 0) *
    J.supA S.G S.de S.de' S.T S.T' S.l (decide (i = 1 ∧ 0 + 1 = 1)) (S.pl v)

theorem g_cast (S : C.HidaSetting E Wp Wq) : ((S.g : ℕ) : ℝ) = S.G.g := by
  unfold C.HidaSetting.g Sz.Glob.g; push_cast; rfl

theorem len_eq (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : S.cutHi v - S.cutLo v = S.G.lenI := by
  simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo, Sz.Glob.lenI, Sz.Glob.place]; ring

theorem T_eq (S : C.HidaSetting E Wp Wq) (hg : 0 < S.G.g) (j : ℕ) :
    ((S.g : ℝ) * lamS S j) / (2 * Real.pi) = (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r (j + 1) 0)) := by
  unfold lamS
  rw [g_cast]
  have hx : 0 < S.G.g / (2 * Real.pi) := by positivity
  have e1 : 2 * Real.pi / S.G.g = (S.G.g / (2 * Real.pi))⁻¹ := by rw [inv_div]
  have key : ∀ n0 n1 : ℤ, n0 = n1 + 1 →
      S.G.g * (S.G.g / (2 * Real.pi)) ^ n1 / (2 * Real.pi) = (2 * Real.pi / S.G.g) ^ (-n0) := by
    intro n0 n1 h
    rw [h, e1, inv_zpow, zpow_neg, inv_inv, zpow_add_one₀ hx.ne']
    field_simp
  exact key _ _ (by unfold S6.nuBlock; push_cast; ring)

end wave

section main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem glob_pos (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : 0 < S.G.g ∧ 0 < S.G.ka := by
  refine ⟨by unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hB.1 hB.2.1, ?_⟩
  unfold Sz.Glob.ka; rw [S.hv]; have := PBD.rd_pos' E; positivity

theorem lenI_pos (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) : 0 < S.G.lenI := by
  have hGo := hB.2.2.2.2.2.2.2.2.2.2.1
  have h := (hGo v).1
  rw [len_eq] at h
  have : (0 : ℝ) < 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop := by have := PBD.ntop_ge S; positivity
  linarith

theorem xw_nonneg (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (i : ℕ) (v : Fin S.f) : 0 ≤ Xw S i v := by
  obtain ⟨hg, hk⟩ := glob_pos hB
  have hl := lenI_pos hB v
  have hN : (0 : ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hA := supA_nonneg S hg hk v (decide (i = 1 ∧ 0 + 1 = 1))
  unfold Xw
  have : 0 < 2 * Real.pi / S.G.g := by positivity
  positivity

theorem thr_wave (hCc : 28 * Real.exp 1 ≤ Cc) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) :
    JC.HidaCurvatureBarriers S (fun i v => Xw S i v) := by
  intro i hi1 _ v
  obtain ⟨hg, hk⟩ := glob_pos hB
  have hl := lenI_pos hB v
  have hCA : Cc ≤ S.CA := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hN : (0:ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hcg : (0:ℝ) ≤ (28 * S.G.N / S.G.lenI) ^ (2 * (i - 1) + 0) := by positivity
  have h := (Formalism.FourierDecayAlt.P.frame_threshold_bound_holds (InfinitePlace E) S.G S.CA S.de S.de' S.T S.T' S.l (S.pl v) hg hl
    (hCc.trans hCA) (fun one => supA_nonneg S hg hk v one)).1 i 0 (Real.exp 1) ((28 * S.G.N / S.G.lenI) ^ (2 * (i - 1) + 0))
    hi1 (Real.exp_pos 1).le le_rfl hcg le_rfl
  refine ⟨xw_nonneg hB i v, ?_⟩
  show Xw S i v ≤ J.thrS S.G S.CA S.de S.de' S.T S.T' S.l i 1 (S.pl v)
  unfold Xw
  exact_mod_cast h

end main

section main2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem xw_K (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (j K : ℕ) (grid : Fin K → Fin (2 * j + 1) → ℝ)
    (hl1 : ∀ b, ∑ i, |F7.lagCo (grid b) i| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ (2 * j)) :
    (∏ b, ∑ i, |F7.lagCo (grid b) i|) * (((S.g : ℝ) * lamS S j) / (2 * Real.pi)) ^ K *
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l (decide (j = 0)) (S.pl v)) ^ K ≤ (Xw S (j + 1) v) ^ K := by
  obtain ⟨hg, hk⟩ := glob_pos hB
  rw [T_eq S hg j]
  have hdec : decide (j + 1 = 1 ∧ 0 + 1 = 1) = decide (j = 0) := by
    by_cases h : j = 0 <;> simp [h]
  have hexp : 2 * (j + 1 - 1) + 0 = 2 * j := by omega
  unfold Xw
  rw [hdec, hexp]
  rw [ntop_eq_N', len_eq] at hl1
  set cg := (28 * S.G.N / S.G.lenI) ^ (2 * j) with hcg
  set Tf := (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r (j + 1) 0)) with hTf
  set A := J.supA S.G S.de S.de' S.T S.T' S.l (decide (j = 0)) (S.pl v) with hA
  have hA0 : 0 ≤ A := supA_nonneg S hg hk v _
  have hprod : (∏ b, ∑ i, |F7.lagCo (grid b) i|) ≤ cg ^ K := by
    calc (∏ b, ∑ i, |F7.lagCo (grid b) i|) ≤ ∏ _b : Fin K, cg :=
          Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun i _ => abs_nonneg _) fun b _ => hl1 b
      _ = cg ^ K := by simp
  have h1 : 0 ≤ Tf ^ K * (Real.exp 1 * A) ^ K := by positivity
  calc (∏ b, ∑ i, |F7.lagCo (grid b) i|) * Tf ^ K * (Real.exp 1 * A) ^ K
      = (∏ b, ∑ i, |F7.lagCo (grid b) i|) * (Tf ^ K * (Real.exp 1 * A) ^ K) := by ring
    _ ≤ cg ^ K * (Tf ^ K * (Real.exp 1 * A) ^ K) := mul_le_mul_of_nonneg_right hprod h1
    _ = (Tf * Real.exp 1 * cg * A) ^ K := by ring

end main2

end

end Formalism.FourierDecayAlt.P.PBL
end

section

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lintegral_base_measure_le {r : ℕ} {TT : ℝ} (H : MA.E r → ENNReal) :
    ∫⁻ q : MA.Qp r TT, H q.1 ∂MA.mu0 r TT ≤ ∫⁻ x in MA.Qset r TT, MA.dens0 x * H x := by
  have hQ : MeasurableSet (MA.Qset r TT) := (MA.Qset_open r TT).measurableSet
  rw [MA.mu0, lintegral_subtype_comap hQ (fun x => H x), restrict_withDensity hQ]
  exact lintegral_withDensity_le_lintegral_mul _ Formalism.FourierDecayAlt.P.MAx2.Adj.density_measurable H

theorem jd_AB_le (k r : ℕ) : B.AB k r ≤ 3 * ((r : ℝ) + 1) ^ 2 * nDim k r := by
  have ha : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hn : nDim k r = 2 * (r : ℝ) + k + 1 := by unfold nDim; push_cast; ring
  unfold B.AB
  rw [hn]
  nlinarith [sq_nonneg (r : ℝ), mul_nonneg ha hb, mul_nonneg (mul_nonneg ha ha) ha, mul_nonneg (mul_nonneg ha ha) hb,
    mul_nonneg (mul_nonneg ha hb) ha]

theorem transfer_square_integrable_holds : TransferSquareIntegrable := by
  refine ⟨3, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr A hA F hCk hCC hFF π
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hPl.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hPl.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' = (D.parOf S v).TT := by rw [hT, hT']; rfl
  have hQm : MeasurableSet (MA.Qset (D.parOf S v).r (D.parOf S v).TT) := (MA.Qset_open _ _).measurableSet

  have hAB : B.AB S.G.k S.G.r ≤ A := (jd_AB_le S.G.k S.G.r).trans hA
  obtain ⟨c0, -, -, hB1, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A hAB
  obtain ⟨C, hC⟩ := hB1
  obtain ⟨c4, hc4⟩ := hCC 4
  have hN : B.normSq Db F ≠ ⊤ := (hC F F c4 c4 (hCC 5) (hCC 5) hc4 hc4).1
  unfold B.normSq jNormSq at hN

  have hsm := Formalism.FourierDecayAlt.P.CutMP.En.trace_smoothness E Wp Wq S T v hPl e hFr (B.JF Db F) hFF π
  have hval := Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem (D.parOf S v) hsm
  refine ⟨((jd_evQ_meas _ _).norm).pow 2, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun q => by positivity)).2 ?_
  set H : MA.E S.G.r → ENNReal := fun x =>
    ENNReal.ofReal (MA.wq S.G.k x (D.parOf S v).TT * ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) with hH
  have p1 : ∀ q : MA.Qp (D.parOf S v).r (D.parOf S v).TT,
      ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e (B.JF Db F) π) q‖ ^ 2) ≤ H q.1 := by
    intro q
    refine ENNReal.ofReal_le_ofReal ?_
    have hq : MA.evQ (D.parOf S v) (trJ S T v e (B.JF Db F) π) q =
        ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1))) := congrFun hval q
    rw [hq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hw := Formalism.FourierDecayAlt.P.CutMP.En.wq_pos (k := S.G.k) q.2
    rw [Real.sq_sqrt hw.le]
    refine mul_le_mul_of_nonneg_left ?_ hw.le
    have he1 : ‖B.hsVec (e π q.1.2)‖ ≤ 1 := by
      have h1 : inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (e π q.1.2)) = (1 : ℂ) := by
        simpa using (hFr.2 q.1.2 q.2.2).2.1 π π
      rw [inner_self_eq_norm_sq_to_K] at h1
      have h2' : ((‖B.hsVec (e π q.1.2)‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
        rw [Complex.ofReal_pow, Complex.ofReal_one]; exact h1
      have h2 : ‖B.hsVec (e π q.1.2)‖ ^ 2 = 1 := Complex.ofReal_injective h2'
      nlinarith [norm_nonneg (B.hsVec (e π q.1.2))]
    have hi : ‖inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1)))‖ ≤
        ‖B.hsVec (B.JF Db F (B.gq Db q.1))‖ :=
      (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (B.hsVec (B.JF Db F (B.gq Db q.1)))])
    exact pow_le_pow_left₀ (norm_nonneg _) hi 2
  have p2 : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x ≤
      ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
        ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := by
    intro x hx
    have hd : MA.dens0 x = ENNReal.ofReal (Formalism.FourierDecayAlt.P.MAx2.Adj.dR x) := by
      unfold MA.dens0 Formalism.FourierDecayAlt.P.MAx2.Adj.dR
      rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _))]
    have hd0 : 0 ≤ Formalism.FourierDecayAlt.P.MAx2.Adj.dR x :=
      Finset.prod_nonneg fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _)
    have hW : bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x =
        Formalism.FourierDecayAlt.P.MAx2.Adj.dR x * MA.wq S.G.k x (D.parOf S v).TT := by
      have hle : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' ≤ Complex.normSq x.2 := by
        rw [hTT]; exact le_of_lt hx.2
      unfold bcWeight
      rw [if_pos hle]
      unfold Formalism.FourierDecayAlt.P.MAx2.Adj.dR MA.wq
      rw [hTT, ← mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun l _ => ?_
      have hM : 2 ≤ MA.Mdim S.G.k S.G.r l := by
        have := l.isLt
        simp only [MA.Mdim]; omega
      have hn : Complex.normSq (x.1 l) ≠ 0 := (Complex.normSq_pos.2 (hx.1 l)).ne'
      have e1 : Formalism.QuantumDeterminants.Mdim S.G.k S.G.r l = MA.Mdim S.G.k S.G.r l := rfl
      rw [e1, pow_mul, Complex.sq_norm, show MA.Mdim S.G.k S.G.r l - 1 = (MA.Mdim S.G.k S.G.r l - 2) + 1 by omega,
        pow_succ]
      field_simp
    rw [hd, hH, ← ENNReal.ofReal_mul hd0, hW, mul_assoc]
  calc ∫⁻ q, ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e (B.JF Db F) π) q‖ ^ 2)
          ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT
        ≤ ∫⁻ q : MA.Qp (D.parOf S v).r (D.parOf S v).TT, H q.1 ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT :=
          lintegral_mono p1
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x := lintegral_base_measure_le H
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT,
            ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_mono' hQm p2
      _ ≤ ∫⁻ x, ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_le_lintegral _ _
      _ < ⊤ := lt_top_iff_ne_top.2 hN

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem phase_holomorphy_holds : GTCPhHol := by
  intro TT u hu h1 R _ hR
  exact Ph.hol_unit (TT := TT) hu (fun ζ hζ => h1 ζ hζ) hR

theorem phase_curvature_holds : GTCPhCurv := by
  intro TT u hu h1 ζ hζ
  exact Ph.curv_unit (TT := TT) hu (fun ζ hζ => h1 ζ hζ) hζ

theorem connection_phase_holds : GTCConnPhase := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e A B u hAB hu hC
  exact connF_phase P (tt_nonneg_of_hyp hyp) Bs d e A B u hAB hC hu

theorem gTCHol_of_ref (hRef : GTCRef) : GTCHol :=
  gTCHol_of_cut hRef phase_relation_holds connection_uniqueness_holds connection_phase_holds phase_holomorphy_holds

theorem gTCCurv_of_ref (hRef : GTCRef) : GTCCurv :=
  gTCCurv_of_cut hRef phase_relation_holds connection_uniqueness_holds connection_phase_holds phase_curvature_holds

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem quadratic_second_shift_form : SSn.Rep.Core.GQQSSF :=
  SSn.Rep.Core.GQ.gQQSSF_of_cut SSn.Rep.Core.GQ.quadratic_transfer_identity SSn.Rep.Core.GQ.quadratic_kappa_identity SSn.Rep.Core.GQ.quadratic_shift_identity

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section

namespace Formalism.FourierDecayAlt.P.CutMP

abbrev JfSmoothBuilt : Prop := JfSmoothDS

end Formalism.FourierDecayAlt.P.CutMP
end
