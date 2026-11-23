module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle087
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle108
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle153
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsTheta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle140
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfChoices
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVZeroOfVanish
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle195
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAtGq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.HmSelfRe
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffForm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormFsvSubOnePow
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle228
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField PI.UnitaryGroupMassFormula.GsFr
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def kcut (t : ℝ) : ℝ := Real.smoothTransition (6 * t - 2)

theorem kcut_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) kcut :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem kcut_zero {t : ℝ} (ht : t ≤ 1 / 3) : kcut t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem kcut_one {t : ℝ} (ht : 1 / 2 ≤ t) : kcut t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

def NrmWFacts : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => PRho.nrmW k r z a) ∧
    ∀ h ∈ UWset k r z, ∀ a, PRho.nrmW k r z (h *ᵥ a) = PRho.nrmW k r z a

theorem nrmW_smul {k r : ℕ} (z a : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    PRho.nrmW k r z (c • a) = Complex.normSq c * PRho.nrmW k r z a := by
  unfold PRho.nrmW
  rw [SSn.Geom.prWv_eq, SSn.Geom.prW_smul, ← SSn.Geom.prWv_eq]
  rw [hm_smul_l, hm_smul_r, ← mul_assoc, Complex.star_def, Complex.mul_conj, Complex.re_ofReal_mul]

section lm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def lmul (A : Wp →L[ℂ] Wp) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := ContinuousLinearMap.compL ℂ Wq Wp Wp A

theorem lmul_apply (A : Wp →L[ℂ] Wp) (X : Wq →L[ℂ] Wp) : lmul A X = A.comp X := rfl

theorem hsInner_lmul (A : Wp →L[ℂ] Wp) (hA : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y)) (X Y : Wq →L[ℂ] Wp) :
    B.hsInner (lmul A X) Y = B.hsInner X (lmul A Y) := by
  simp only [B.hsInner, B.hsVec, lmul_apply, PiLp.inner_apply, ContinuousLinearMap.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA]

end lm

theorem typeProj_of (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines) (hDU : SSn.Rep.DatumUnit)
    (hNW : NrmWFacts) : TypeProj := by
  refine ⟨0, le_rfl, ?_⟩
  intro Cc _ E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  by_cases hk : 2 ≤ S.G.k
  · obtain ⟨Pr, hs, heqv, hrest⟩ := hPE (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hPl hk
    obtain ⟨hnc, hninv⟩ := hNW S.G.k S.G.r (T v).base.z (T v).base.z_mem (T v).base.T_pos
    refine ⟨fun σ a => ((kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) : ℝ) : ℂ) • lmul (Pr σ a), ?_, ?_, ?_, ?_⟩
    ·
      intro σ
      rw [contDiff_iff_contDiffAt]
      intro a₀
      by_cases h : 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a₀
      · have hO : IsOpen {a | 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a} :=
          isOpen_lt continuous_const hnc.continuous
        have hl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun A : Wp (S.pl v) →L[ℂ] Wp (S.pl v) => (lmul A : (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] _)) :=
          (ContinuousLinearMap.compL ℂ (Wq (S.pl v)) (Wp (S.pl v)) (Wp (S.pl v))).contDiff.restrict_scalars ℝ
        have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun a => ((kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) : ℝ) : ℂ) • lmul (Pr σ a))
            {a | 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a} :=
          ((Complex.ofRealCLM.contDiff.comp (kcut_contDiff.comp hnc)).contDiffOn).smul
            (hl.comp_contDiffOn (hs σ))
        exact h1.contDiffAt (hO.mem_nhds h)
      · have hO : IsOpen {a | PRho.nrmW S.G.k S.G.r (T v).base.z a < 1 / 3} :=
          isOpen_lt hnc.continuous continuous_const
        have hmem : a₀ ∈ {a | PRho.nrmW S.G.k S.G.r (T v).base.z a < 1 / 3} := by
          simp only [Set.mem_setOf_eq]; linarith [not_lt.1 h]
        refine (contDiffAt_const (c := (0 : (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v))))).congr_of_eventuallyEq ?_
        filter_upwards [hO.mem_nhds hmem] with a ha
        simp [kcut_zero (le_of_lt ha)]
    ·
      intro σ a A B'
      dsimp only
      by_cases h : 0 < PRho.nrmW S.G.k S.G.r (T v).base.z a
      · rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, kap_hsInner_smul_left,
          kap_hsInner_smul_right, Complex.conj_ofReal, hsInner_lmul _ ((hrest a h).2.1 σ)]
      · have h0 : kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) = 0 := kcut_zero (by linarith [not_lt.1 h])
        simp [h0, B.hsInner, kap_hsVec_zero]
    ·
      intro σ h hh h' hh' a X
      have hinv : h⁻¹ ∈ UWset S.G.k S.G.r (T v).base.z := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
      have hu := WeylGroupFacts.isUnit_of_uh hh.1
      have hh1 : h⁻¹ * h = 1 := by
        first
          | exact Matrix.nonsing_inv_mul _ hu
          | exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
      have key : ∀ y, (T v).base.π h⁻¹ ((T v).base.π h y) = y := by
        intro y
        rw [← ContinuousLinearMap.comp_apply, ← (T v).base.π_rep.2 _ hinv _ hh, hh1, (T v).base.π_rep.1]
        rfl
      dsimp only
      rw [hninv h hh a, heqv h hh σ a]
      ext y
      simp [lmul_apply, key]
    ·
      intro x hx σ ρ
      dsimp only
      obtain ⟨hP1, hH1, -, -⟩ := hDU Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v x.2 hx.2
      set n0 := SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec x.2 with hn0
      have hN0 : PRho.nrmW S.G.k S.G.r (T v).base.z n0 = 1 := by
        unfold PRho.nrmW; rw [hP1, hH1]; simp
      have hph : SSn.phD x.1 ≠ 0 := by
        intro h0
        have := SSn.Geom.phD_norm hx.1
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      have hN : PRho.nrmW S.G.k S.G.r (T v).base.z (SSn.phD x.1 • n0) = 1 := by
        rw [nrmW_smul, hN0, mul_one, Complex.normSq_eq_norm_sq, SSn.Geom.phD_norm hx.1]; norm_num
      have hscale : ∀ τ, Pr τ (SSn.phD x.1 • n0) = Pr τ n0 :=
        fun τ => (hrest n0 (by rw [hN0]; norm_num)).1 τ _ hph
      have hfix : ∀ y, Pr ρ n0 (e ρ x.2 y) = e ρ x.2 y := by
        intro y
        refine ((hrest n0 (by rw [hN0]; norm_num)).2.2.2 ρ (e ρ x.2 y)).2 ?_
        intro Fr hFrm w
        rw [hP1] at hFrm
        exact hGL Cc E Wp Wq S T f χ ν' m₀ top A₀ v e ⟨hB, hFr, hGa, hQQ⟩ hk x.2 hx.2 ρ Fr hFrm w y
      rw [ContinuousLinearMap.smul_apply, hN, kcut_one (by norm_num), lmul_apply, hscale]
      simp only [Complex.ofReal_one, one_smul]
      by_cases hσ : σ = ρ
      · subst hσ
        rw [if_pos rfl]
        ext y
        exact hfix y
      · rw [if_neg hσ]
        ext y
        have horth := (hrest n0 (by rw [hN0]; norm_num)).2.2.1 σ ρ
        rw [if_neg hσ] at horth
        rw [ContinuousLinearMap.comp_apply, ← hfix y, ← ContinuousLinearMap.comp_apply (Pr σ n0), horth]
        rfl
  ·
    have hk1 : (D.parOf S v).k - 1 = 0 := by
      have : (D.parOf S v).k = S.G.k := rfl
      omega
    have hsub : ∀ σ ρ : M.Ty (D.parOf S v), σ = ρ := by
      intro σ ρ
      funext i
      exact absurd i.2 (by omega)
    refine ⟨fun _ _ => ContinuousLinearMap.id ℂ _, fun σ => contDiff_const, fun σ a A B' => rfl,
      fun σ h _ h' _ a X => rfl, ?_⟩
    intro x _ σ ρ
    rw [if_pos (hsub σ ρ)]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.GA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem gAJComm_of_thetaJ (hT : LT.ThetaJ) : GAJComm := by
  refine ⟨12, 0, by norm_num, le_rfl, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ d Bg hd hBg hΘ _hCoef η F _hη hFs hFg _hFsupp
    U J hU hJ hagree x hx hxU
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hBg0 : 0 ≤ Bg := le_trans (by simp) hBg

  have hAg := LT.agreement_on_domain_holds S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base J F U hJ
    (fun q hq hqU => hagree q ⟨hq.1, by rw [hTT]; exact hq.2⟩ hqU)
  set V : Set (B.Mat S.G.k S.G.r) := Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
    (fun g => Gf S.G.k S.G.r (T v).base.z (T v).base.z' g) ⁻¹' U with hVdef
  have hVo : IsOpen V := (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open _ _).inter
    (hU.preimage (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont _ _))
  have hJV : ∀ y ∈ V, y ∈ B.GV S.G.k S.G.r → J y = B.JF (T v).base F y := fun y hy hyG =>
    hAg y ⟨hyG, hy.1⟩ hy.2
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, by rw [← hTT]; exact hx.2⟩
  have hg0 := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hg0V : B.gq (T v).base x ∈ V := ⟨hg0.2, hxU⟩

  have hJck : B.CkOn ⊤ (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') J :=
    Formalism.FourierDecayAlt.P.CutMP.jdc_ckOn_om _ _ hJ.1
  set UU : Set (B.Mat S.G.k S.G.r) := JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' ∩ V with hUUdef
  have hUU : UU ⊆ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' := Set.inter_subset_left
  have hCkF : B.CkOn (B.opOrder Θ : ℕ∞) UU (B.JF (T v).base F) := by
    intro g₀ hg₀
    obtain ⟨U₁, f', hU₁, hgU₁, hc, he⟩ := hJck g₀ hg₀.1
    refine ⟨U₁ ∩ V, f', hU₁.inter hVo, ⟨hgU₁, hg₀.2⟩, (hc.mono Set.inter_subset_left).of_le ?_, ?_⟩
    · exact_mod_cast le_top
    · intro g hg hgG
      rw [← hJV g hg.2 hgG]
      exact he g hg.1 hgG
  have hg0UU : B.gq (T v).base x ∈ UU := ⟨hg0, hg0V⟩

  have hThr : Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold S.G.k S.G.r
      (B.AB S.G.k S.G.r + 12 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5) -
        Bg * ((B.opOrder Θ : ℕ) : ℝ)) (B.opOrder Θ) := by
    have hAB : (0 : ℝ) ≤ B.AB S.G.k S.G.r := by unfold B.AB; positivity
    have hr : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
    have ho : (0 : ℝ) ≤ (B.opOrder Θ : ℝ) := Nat.cast_nonneg _
    apply Formalism.FourierDecayAlt.P.CutMP.jdc_thrW (B.opOrder Θ) _ (B.AB S.G.k S.G.r + 30 * (S.G.r : ℝ) + d +
      Bg * ((B.opOrder Θ : ℝ) + 10)) (by positivity)
    linarith
  obtain ⟨hT1, hT2⟩ := hT S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base Θ _ F UU hThr hΘ.1 hΘ.2 hFs
    (hFg (B.opOrder Θ)) hUU hCkF

  have hg0G : B.gq (T v).base x ∈ B.GV S.G.k S.G.r := hg0.1
  refine ⟨?_, ?_⟩
  · rw [← hT1 _ hg0]
    unfold B.opApply
    congr 1
    apply List.map_congr_left
    intro Tm _
    rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local Tm.word Tm.word_lie hVo hJV _ hg0V hg0G]
  · rw [← hT2 _ hg0UU]
    unfold B.opAdj
    congr 1
    apply List.map_congr_left
    intro Tm _
    rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local Tm.word.reverse
      (fun X hX => Tm.word_lie X (List.mem_reverse.1 hX)) hVo
      (f := fun y => Tm.coefAdj y (J y)) (f' := fun y => Tm.coefAdj y (B.JF (T v).base F y))
      (fun y hy hyG => by simp only [hJV y hy hyG]) _ hg0V hg0G]

theorem gAJComm_of_adjComm (hAC : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AdjComm) : GAJComm :=
  gAJComm_of_thetaJ (LT.thetaJ_of_adjComm hAC)

end Formalism.FourierDecayAlt.P.CutMP.JA.GA

end
end

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section C1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem block0C (hA : P5.ThmPActualCpt) (hPSC : StandardPairingDecay.PStdC) (hVI : KB.VIsoCpt) (hFP : FormPosCpt)
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (Y : Finset C.LPt)
    (hY : ∀ h ∈ Y, D.ptSize h = j) :
    KB.BlockPSD Y Y (KB.gN (setC S p F) v ε j w) (KB.hatB (setC S p F) v ε (j + 1) 1 w l)
      (KB.gN (setC S p F) v ε j w) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hw' : KB.CutWord (D.parOf S v) (p v).l0 w := by rw [hl0]; exact hw
  set Dv := CV ((p v).T.bs j) (S := Fin w.length) with hDv
  refine block_iso Dv ((p v).form j hj w) cv_zero (fun x y hx hy => cv_add hx hy) (fun c x hx => cv_smul c hx)
    (fun x₁ x₂ y c h₁ h₂ hy => form_slC (p v) j hj w x₁ x₂ y c h₁ h₂ hy)
    (fun x y₁ y₂ c hx h₁ h₂ => form_srC (p v) j hj w x y₁ y₂ c hx h₁ h₂)
    (fun x hx => hFP hA _ _ (D.parOf S v) (p v) j hj w hw' x hx)
    (KB.waveG ((p v).T.bs j) (sW S j l) w) (fun x hx => (hVI hA _ _ (D.parOf S v) (p v) j hj w hw' (sW S j l) x x hx hx).1)
    (fun x y hx hy => (hVI hA _ _ (D.parOf S v) (p v) j hj w hw' (sW S j l) x y hx hy).2)
    Y (uY S p F v ε j hj w Y) (fun h => uY_cv hB F hF v ε hε j hj w Y h)
    (1 / (ΓS S j * S.sizeAt v w)) ?_ _ _ ?_ ?_
  · have : 0 ≤ ΓS S j * S.sizeAt v w := by
      refine mul_nonneg ?_ (sizeAt_nonneg S v w)
      unfold ΓS
      have hgpos := g_pos_of_built hB
      have hrd := PBD.rd_pos' E
      exact (PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _).le
    positivity
  · intro h hh h' hh'
    rw [uY_mem S p F v ε j hj w Y h hh, uY_mem S p F v ε j hj w Y h' hh']
    exact gN_uB hB F hF v ε hε j hj w h h'
  · intro h hh h' hh'
    rw [uY_mem S p F v ε j hj w Y h hh, uY_mem S p F v ε j hj w Y h' hh']
    exact hatB_uB_C hPSC hB F hF v ε hε j hj w hw l h h' (hY h hh) (hY h' hh')

theorem gN_psdC (hA : P5.ThmPActualCpt) (hFP : FormPosCpt) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (Y : Finset C.LPt) :
    TB.PSDOn Y (KB.gN (setC S p F) v ε j w) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hw' : KB.CutWord (D.parOf S v) (p v).l0 w := by rw [hl0]; exact hw
  set c0 : ℝ := 1 / (ΓS S j * S.sizeAt v w) with hc0
  have hc0n : 0 ≤ c0 := by
    have := gam_pos hB j
    have := sizeAt_nonneg S v w
    positivity
  set Dv := CV ((p v).T.bs j) (S := Fin w.length) with hDv
  have hG := gram_psd Dv (fun x y => (c0 : ℂ) * (p v).form j hj w x y) cv_zero (fun x y hx hy => cv_add hx hy)
    (fun c x hx => cv_smul c hx)
    (fun x₁ x₂ y c h₁ h₂ hy => by simp only [form_slC (p v) j hj w x₁ x₂ y c h₁ h₂ hy]; ring)
    (fun x y₁ y₂ c hx h₁ h₂ => by simp only [form_srC (p v) j hj w x y₁ y₂ c hx h₁ h₂]; ring)
    (fun x hx => mul_nonneg (by exact_mod_cast hc0n) (hFP hA _ _ (D.parOf S v) (p v) j hj w hw' x hx))
    Y (uY S p F v ε j hj w Y) (fun h => uY_cv hB F hF v ε hε j hj w Y h)
  refine psd_congr (fun x hx y hy => ?_) hG
  show (c0 : ℂ) * (p v).form j hj w (uY S p F v ε j hj w Y x) (uY S p F v ε j hj w Y y) = _
  rw [uY_mem S p F v ε j hj w Y x hx, uY_mem S p F v ε j hj w Y y hy, gN_uB hB F hF v ε hε j hj w x y]

end C1

end

end Formalism.FourierDecayAlt.P.PBL
end

section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vanish_kr (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    {H : B.Mat k n → (Wq →L[ℂ] Wp)} {Cs : Set (B.Mat k n)} (hH : ∀ g ∈ B.GV k n, g ∉ Cs → H g = 0)
    {U : Set (B.Mat k n)} (hP : Proper Bj B0 e Cs U) : VanishL Bj e (PBG.Kr B0 H) U := by
  intro y hy
  obtain ⟨V, hV, K, hK, hVK⟩ := hP y hy
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.2 hV, K, hK, fun g hg hgG x hx hxK => ?_⟩
  rw [Formalism.FourierDecayAlt.P.PBG.kr_eq]
  rw [← integral_zero (Mt k n × Mt k n) (Wq →L[ℂ] Wp)]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.PBG.ae_inR B0] with ξ hξ
  rw [Formalism.FourierDecayAlt.P.PBG.rho_pR]
  have hG : sE Bj e x * g * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ B.GV k n :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (sE_GV Bj e x) hgG) hξ.2.1) hξ.1.1
  have hC := hVK g (interior_subset hg) hgG x hx hxK ξ hξ
  rw [hH _ hG hC]
  simp

end Formalism.FourierDecayAlt.P.PartialBesselProperness
end
end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.FourierDecayAlt

def DecayUnifOfHeads : Prop := KB.RadHead → KB.HeadTop → DecayUnif

theorem decayUnifOfHeads : DecayUnifOfHeads := fun hRH hHT =>
  decayUnif_of hRH hHT Formalism.FourierDecayAlt.P.wave_difference_form

end Formalism.FourierDecayAlt.P.PBO

theorem Formalism.FourierDecayAlt.P.uniform_decay_of_heads : Formalism.FourierDecayAlt.P.PBO.DecayUnifOfHeads := Formalism.FourierDecayAlt.P.PBO.decayUnifOfHeads
end
end
