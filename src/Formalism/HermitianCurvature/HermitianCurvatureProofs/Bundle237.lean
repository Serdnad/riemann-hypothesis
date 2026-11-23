module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle068
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle108
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle134
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLMinusPosOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle235
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle186
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle087
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle200
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle233
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsTheta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle163
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle140
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle234
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle232
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle223
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle229
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem thrW_sa (k r o : ℕ) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r (6 * (r : ℝ) * (o : ℝ) + (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ)) * (6 * (r : ℝ) + 1) + 1) o := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h1 : 0 ≤ (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ)) * (6 * (r : ℝ) + 1) := by positivity
  have h2 : 0 ≤ (r : ℝ) * (6 * (r : ℝ) + 1) := by positivity
  refine ⟨by linarith, ?_⟩
  nlinarith

theorem sAJCommC_of_thetaJ (hT : LT.ThetaJ) : SAJCommC := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ hΘ F hFs hFc _hFO U X hU hX hagree y hy hyU
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl

  have hAg := QO.agree_qOf (T v).base X F U hX
    (fun q hq hqU => hagree q ⟨hq.1, by rw [hTT]; exact hq.2⟩ hqU)
  set V : Set (B.Mat S.G.k S.G.r) := Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
    QO.qOf (T v).base.z (T v).base.z' ⁻¹' U with hVdef
  have hVo : IsOpen V := QO.isOpen_qOf _ _ hU
  have hJV : ∀ g ∈ V, g ∈ B.GV S.G.k S.G.r → X g = B.JF (T v).base F g := fun g hg hgG =>
    hAg g ⟨hgG, hg.1⟩ hg.2
  have hq : y ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hy.1, by rw [← hTT]; exact hy.2⟩
  have hg0 := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hg0V : B.gq (T v).base y ∈ V := ⟨hg0.2, by
    show QO.qOf (T v).base.z (T v).base.z' (B.gq (T v).base y) ∈ U
    rw [QO.qOf_gq (T v).base hq]; exact hyU⟩

  have hJck : B.CkOn ⊤ (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') X :=
    Formalism.FourierDecayAlt.P.CutMP.jdc_ckOn_om _ _ hX.1
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
  have hg0UU : B.gq (T v).base y ∈ UU := ⟨hg0, hg0V⟩

  have hIn := Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hFs hFc
    (fun g _ hg => image_eq_zero_of_notMem_tsupport hg)
    (6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) +
      (S.G.r : ℝ) * (4 * (S.G.r : ℝ) + 2 * (S.G.k : ℝ)) * (6 * (S.G.r : ℝ) + 1) + 1) (B.opOrder Θ)
  obtain ⟨hT1, hT2⟩ := hT S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base Θ _ F UU
    (thrW_sa S.G.k S.G.r (B.opOrder Θ)) hΘ.1 hΘ.2 hFs hIn hUU hCkF
  have hg0G : B.gq (T v).base y ∈ B.GV S.G.k S.G.r := hg0.1
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
      (f := fun g => Tm.coefAdj g (X g)) (f' := fun g => Tm.coefAdj g (B.JF (T v).base F g))
      (fun g hg hgG => by simp only [hJV g hg hgG]) _ hg0V hg0G]

theorem sAJCommC_of_adjComm (hAC : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AdjComm) : SAJCommC :=
  sAJCommC_of_thetaJ (LT.thetaJ_of_adjComm hAC)

theorem self_adjoint_commutation_compact : SAJCommC :=
  sAJCommC_of_adjComm Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjoint_commutation_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SA

end
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem smooth_forms_stability_holds : JAFFStable := FFS.jAFFStable_of_adjComm FFS.adjoint_commutation_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jABddKapQQ_of_shared (hG : SSn.SSnGeom) (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines)
    (hDU : SSn.Rep.DatumUnit) : JABddKapQQ :=
  jABddKapQQ_of_cut hG hPE hGL hDU weighted_norm_facts_hold

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section

namespace Formalism.FourierDecayAlt.P.CutHL

theorem head_letter_of_minus_positive : LevelPointCoordinates.HeadLetter :=
  headLetter_of_minusPos Formalism.FourierDecayAlt.P.minus_positive_of_parts

end Formalism.FourierDecayAlt.P.CutHL

theorem Formalism.FourierDecayAlt.P.head_letter_identity : Formalism.FourierDecayAlt.P.LevelPointCoordinates.HeadLetter := Formalism.FourierDecayAlt.P.CutHL.head_letter_of_minus_positive
end

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem norm_fsv_rd (s t : ℂ) : ‖fsv s t‖ = 1 := by
  unfold fsv
  rw [Complex.norm_exp]
  have h : (s * t - (starRingEnd ℂ) s * (starRingEnd ℂ) t).re = 0 := by
    rw [← map_mul, Complex.sub_re, Complex.conj_re, sub_self]
  rw [h, Real.exp_zero]

theorem hsVec_smul_rd {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℂ) (A : Wq →L[ℂ] Wp) :
    B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  rfl

theorem radial_boundedness : RDBdd := by
  intro k r Wp Wq _ _ _ _ _ _ D F H _ _
  refine ⟨∫ q, ‖(bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D H (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q)))‖, fun s => ?_⟩
  have h1 : 1 < r + 2 := by omega
  have hinv : ∀ p : B.SS k r, D.inSS p → ∀ g,
      fsv s (Dmin k r D.z D.z' (B.sgs p g) ⟨1, h1⟩) = fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩) := fun p hp g => by
    rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs D hp g]
  have hJ : ∀ g, B.JF D (wvG D.z D.z' s F) g = fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩) • B.JF D F g := fun g =>
    Formalism.FourierDecayAlt.P.PBFV.JF_mul_inv D _ hinv F g
  unfold B.beta betaBig
  refine (norm_integral_le_integral_norm _).trans
    (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)))
  show ‖(bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D H (B.gq D q))) (B.hsVec (B.JF D (wvG D.z D.z' s F) (B.gq D q)))‖ = _
  rw [hJ, hsVec_smul_rd, inner_smul_right]
  simp only [norm_mul, norm_fsv_rd, one_mul]

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_wave_identity : RDWave := by
  intro k r Wp Wq _ _ _ _ _ _ D hr ε s G
  have h1 : 1 < r + 2 := by omega
  refine ⟨fun hG => Formalism.FourierDecayAlt.P.PBFV.good_fsv_dmin D ε s h1 G hG, fun y hy => ?_⟩
  have hinv : ∀ p : B.SS k r, D.inSS p → ∀ g,
      fsv s (Dmin k r D.z D.z' (B.sgs p g) ⟨1, h1⟩) = fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩) := fun p hp g => by
    rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs D hp g]
  simp only [resG]
  rw [show wvG D.z D.z' s G = fun g => fsv s (Dmin k r D.z D.z' g ⟨1, h1⟩) • G g from rfl,
    Formalism.FourierDecayAlt.P.PBFV.JF_mul_inv D _ hinv G]
  rw [Formalism.FourierDecayAlt.P.PBFV.first_minor_cell_eq_coord D.z_mem D.z'_mem hr y.1 hy.2.1 h1]
  exact smul_comm _ _ _

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_beta_identity : RDBeta := by
  intro k r Wp Wq _ _ _ _ _ _ D μ hμ
  obtain ⟨C1, hC1, hpair⟩ := Formalism.FourierDecayAlt.P.JCx2.rb_pairAt D μ hμ
  refine ⟨(C1 : ℂ), by exact_mod_cast hC1.ne', fun F H Φ Ψ hF hH hΦ hΨ c => ?_⟩
  have h := Formalism.FourierDecayAlt.P.JCx2.rb_main D μ C1 hpair (n := 0) (fun _ => F) (fun _ => H) (fun _ => Φ) (fun _ => Ψ)
    (fun _ => hF) (fun _ => hH) (fun _ => hΦ) (fun _ => hΨ)
  have hsum : ∑ _a : Wd.Ix (Fin 0), B.beta D F H = B.beta D F H := by simp
  rw [hsum] at h
  rw [← h]
  unfold LocFacts₂ P5.form
  refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
  have hg : glue (0 : Fin (r + 1)) c c' = glue 0 0 c' := by
    funext l
    simp only [glue]
    have h0 : ((0 : Fin (r + 1)) : ℕ) ≤ (l : ℕ) := Nat.zero_le _
    rw [dite_eq_left h0, dite_eq_left h0]
  simp only [hg, Finset.univ_unique, Finset.sum_singleton]

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem conj_phD_sq {r : ℕ} {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) :
    (conj (SSn.phD c)) ^ 2 = (∏ i, conj (c i)) * ∏ i, (c i)⁻¹ := by
  have hP : (∏ i, c i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a
  rw [← map_prod, Finset.prod_inv_distrib]
  unfold SSn.phD
  set D := ∏ i, c i with hD
  have hn : ((‖D‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hP
  have hnn : ((‖D‖ : ℝ) : ℂ) ^ 2 = D * conj D := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [map_div₀, Complex.conj_ofReal, div_pow, hnn]
  field_simp

section gen

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem cd_comp {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {U V W : Type} [NormedAddCommGroup U]
    [NormedSpace ℂ U] [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {n : WithTop ℕ∞} {g : X → V →L[ℂ] W} {f : X → U →L[ℂ] V} (hg : ContDiff ℝ n g) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => (g x).comp (f x)) :=
  ((ContinuousLinearMap.compL ℂ U V W).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp (hg.prodMk hf)

theorem hsVec_zero' : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsVec; ext i; simp

theorem hsInner_zero_l (B' : Wq →L[ℂ] Wp) : B.hsInner (0 : Wq →L[ℂ] Wp) B' = 0 := by
  unfold B.hsInner; rw [hsVec_zero', inner_zero_right]

theorem hsInner_zero_r (A : Wq →L[ℂ] Wp) : B.hsInner A (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsInner; rw [hsVec_zero', inner_zero_left]

theorem inner_hs_smul (c : ℂ) (A B' : Wq →L[ℂ] Wp) :
    inner ℂ (B.hsVec A) (B.hsVec (c • B')) = c * inner ℂ (B.hsVec A) (B.hsVec B') := by
  rw [Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right]

theorem mat_gen {Ty : Type} [Fintype Ty] [DecidableEq Ty] (Qd : Ty → (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))
    (T0 : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (c : Ty → Ty → ℂ) (e : Ty → (Wq →L[ℂ] Wp))
    (hQadj : ∀ σ A B', B.hsInner (Qd σ A) B' = B.hsInner A (Qd σ B'))
    (hline : ∀ σ ρ, Qd σ (e ρ) = if σ = ρ then e ρ else 0) (π ρ : Ty) :
    B.hsInner (∑ π', ∑ ρ', c π' ρ' • Qd ρ' (T0 (Qd π' (e π)))) (e ρ) = c π ρ * B.hsInner (T0 (e π)) (e ρ) := by
  rw [kap_hsInner_sum_left, Finset.sum_eq_single π]
  · rw [kap_hsInner_sum_left, Finset.sum_eq_single ρ]
    · rw [kap_hsInner_smul_left, hQadj, hline π π, hline ρ ρ, if_pos rfl, if_pos rfl]
    · intro ρ' _ hne
      rw [kap_hsInner_smul_left, hQadj, hline ρ' ρ, if_neg hne, hsInner_zero_r, mul_zero]
    · intro h; exact absurd (Finset.mem_univ ρ) h
  · intro π' _ hne
    rw [hline π' π, if_neg hne, map_zero]
    simp only [map_zero, smul_zero, Finset.sum_const_zero]
    exact hsInner_zero_l _
  · intro h; exact absurd (Finset.mem_univ π) h

theorem mat_gen' {Ty : Type} [Fintype Ty] [DecidableEq Ty] (Qd : Ty → (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))
    (T0 : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (c : Ty → Ty → ℂ) (e : Ty → (Wq →L[ℂ] Wp))
    (hQadj : ∀ σ A B', B.hsInner (Qd σ A) B' = B.hsInner A (Qd σ B'))
    (hline : ∀ σ ρ, Qd σ (e ρ) = if σ = ρ then e ρ else 0) (π ρ : Ty) :
    inner ℂ (B.hsVec (e ρ)) (B.hsVec ((∑ π', ∑ ρ', c π' ρ' • (Qd ρ').comp (T0.comp (Qd π'))) (e π))) =
      c π ρ * inner ℂ (B.hsVec (e ρ)) (B.hsVec (T0 (e π))) := by
  have h := mat_gen Qd T0 c e hQadj hline π ρ
  unfold B.hsInner at h
  rw [← h]
  congr 2
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.comp_apply]

theorem sandw_apply (A : Wp →L[ℂ] Wp) (B' : Wq →L[ℂ] Wq) (X : Wq →L[ℂ] Wp) : sandw A B' X = A.comp (X.comp B') := rfl

end gen

theorem ssnRep_of (hTP : TypeProj) (hTF : ThtFacts) (hTG : ThtGaugeConst) : SSnRep := by
  obtain ⟨K, hK, hTP⟩ := hTP
  refine ⟨K, hK, ?_⟩
  intro Cc hCc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ l hl
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hk : 2 ≤ S.G.k := by
    have := (Finset.mem_Icc.1 hl)
    have h2 : (D.parOf S v).k = S.G.k := rfl
    omega
  obtain ⟨Qp, hQs, hQadj, hQeq, hQline⟩ := hTP Cc hCc E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ
  obtain ⟨Bw, hBw⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists (T v).base.z_mem (T v).base.T_pos
  obtain ⟨Bw', hBw'⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists (T v).base.z'_mem (T v).base.T'_pos
  obtain ⟨hc, hca, hadj, heqv, hph⟩ := hTF (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hPl Bw Bw' hBw hBw'
  obtain ⟨κ, hκ⟩ := hTG Cc E Wp Wq S T f χ ν' m₀ top A₀ v e ⟨hB, hFr, hGa, hQQ⟩ hk l hl Bw Bw' hBw hBw'
  classical
  set th := tht S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' Bw Bw' with hth
  set thA := thtA S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' Bw Bw' with hthA
  refine ⟨fun a a' ι => ∑ π, ∑ ρ, (if M.Up (D.parOf S v) l π ρ then κ π else 0) •
      (Qp ρ a).comp ((th a a' ι).comp (Qp π a)),
    fun a a' ι => ∑ π, ∑ ρ, (if M.Up (D.parOf S v) l π ρ then conj (κ π) else 0) •
      (Qp π a).comp ((thA a a' ι).comp (Qp ρ a)), ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ContDiff.sum fun π _ => ContDiff.sum fun ρ _ => ContDiff.const_smul _ ?_
    exact cd_comp ((hQs ρ).comp contDiff_fst) (cd_comp hc ((hQs π).comp contDiff_fst))
  · refine ContDiff.sum fun π _ => ContDiff.sum fun ρ _ => ContDiff.const_smul _ ?_
    exact cd_comp ((hQs π).comp contDiff_fst) (cd_comp hca ((hQs ρ).comp contDiff_fst))
  ·
    intro a a' ι A B'
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]
    rw [kap_hsInner_sum_left, kap_hsInner_sum_right]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [kap_hsInner_sum_left, kap_hsInner_sum_right]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [kap_hsInner_smul_left, kap_hsInner_smul_right, hQadj, hadj, hQadj]
    congr 1
    split_ifs <;> simp
  ·
    intro h hh h' hh' a a' ι X
    have hsum : ∀ (F : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) →
        ((Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))),
        ((T v).base.π h).comp (((∑ π, ∑ ρ, F π ρ) X).comp ((T v).base.π' h'⁻¹)) =
          ∑ π, ∑ ρ, ((T v).base.π h).comp ((F π ρ X).comp ((T v).base.π' h'⁻¹)) := by
      intro F
      have := map_sum (sandw ((T v).base.π h) ((T v).base.π' h'⁻¹)) (fun π => (∑ ρ, F π ρ) X) Finset.univ
      simp only [sandw_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply] at this ⊢
      rw [this]
      refine Finset.sum_congr rfl fun π _ => ?_
      exact map_sum (sandw ((T v).base.π h) ((T v).base.π' h'⁻¹)) (fun ρ => F π ρ X) Finset.univ
    constructor
    · rw [hsum]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]
      refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun ρ _ => ?_
      rw [hQeq π h hh h' hh' a X, (heqv h hh h' hh' a a' ι _).1, hQeq ρ h hh h' hh' a _]
      split_ifs <;> ext y <;> simp
    · rw [hsum]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]
      refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun ρ _ => ?_
      rw [hQeq ρ h hh h' hh' a X, (heqv h hh h' hh' a a' ι _).2, hQeq π h hh h' hh' a _]
      split_ifs <;> ext y <;> simp
  ·
    intro q hq ρ π
    have hq1 : ∀ a, q.1 a ≠ 0 := hq.1
    have hζ : (D.parOf S v).TT < Complex.normSq q.2 := hq.2
    have hline := hQline q hq
    refine (mat_gen' (fun σ => Qp σ (SSn.phD q.1 • SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2))
      (th (SSn.phD q.1 • SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2)
        (conj (SSn.phD q.1) • SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2)
        (SSn.io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2))
      (fun π' ρ' => if M.Up (D.parOf S v) l π' ρ' then κ π' else 0) (fun σ => e σ q.2)
      (fun σ => hQadj σ _) hline π ρ).trans ?_
    rw [hph (SSn.phD q.1), ContinuousLinearMap.smul_apply, inner_hs_smul]
    unfold SSn.ssnV
    split_ifs with hup
    · have h1 := hκ q.2 hζ π ρ hup
      rw [← conj_phD_sq hq1]
      linear_combination (conj (SSn.phD q.1)) ^ 2 * h1
    · simp

theorem second_shift_representation_assembly : SSnRepOfCut := fun hPE hGL hTF hDU hTG =>
  ssnRep_of (typeProj_of hPE hGL hDU weighted_norm_facts_hold) hTF hTG

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem local_adjoint_transfer_holds : JALocAdj := jALocAdj_of_adjComm FFS.adjoint_commutation_holds

theorem local_class_transfer_holds : JALocCC := jALocCC_of_op local_operator_transfer_holds local_adjoint_transfer_holds

theorem group_action_commutation_holds : GA.GAJComm := GA.gAJComm_of_adjComm FFS.adjoint_commutation_holds

theorem group_adjoint_transfer_holds : JAGroupAdj := jAGroupAdj_of_jComm group_action_commutation_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end
