module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle301
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle393
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle104
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle302
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle278
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle022
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle279
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle312
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle372
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacter
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle395
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle199
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle273
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle075
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle090
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne

@[expose] public section

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_gluedLattices_iff_existsUnique_localDatum : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → ∀ Λ : LV D, (Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ ∃ y : Dat Z FP, Λ ∈ globSet G G' y) ∧ (∀ y y' : Dat Z FP, Λ ∈ globSet G G' y → Λ ∈ globSet G G' y' → y = y') ∧ (∀ y : Dat Z FP, Λ ∈ globSet G G' y → (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) ∧ {p | y p ≠ d0 p}.Finite) ∧ ∀ (y y' : Dat Z FP), ∀ h ∈ H0 F F', RMoves h y y' → (Λ ∈ globSet G G' y ↔ Formalism.HermitianLatticesTheory.gmap h Λ ∈ globSet G G' y') := by
  first | exact @GlobalTheory.GlueDat.glued_data | exact GlobalTheory.GlueDat.glued_data | (intros; apply GlobalTheory.GlueDat.glued_data <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.BeRankOne

theorem exists_rankOne_of_hermitian_nonneg_operatorKernel {H Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (V : Set H) (B : H → H → (Wp →L[ℂ] Wp)) (l₀ : H → Wp)
    (hc : ∀ v ∈ V, ∀ ξ : Wp, ∃ c : ℂ, ∀ u ∈ V, B u v ξ = c • l₀ u)
    (hadj : ∀ u ∈ V, ∀ v ∈ V, ContinuousLinearMap.adjoint (B u v) = B v u)
    (hpos : ∀ v ∈ V, ∀ ξ : Wp, 0 ≤ (⟪ξ, B v v ξ⟫_ℂ).re ∧ (⟪ξ, B v v ξ⟫_ℂ).im = 0)
    (hne : ∃ u ∈ V, ∃ v ∈ V, ∃ ξ : Wp, B u v ξ ≠ 0) :
    ∃ t : ℂ, (∃ u ∈ V, t • l₀ u ≠ 0) ∧ ∀ u ∈ V, ∀ v ∈ V, B u v = rk1 (t • l₀ u) (t • l₀ v) := by
  classical
  obtain ⟨u₁, hu₁, v₁, hv₁, ξ₁, hne₁⟩ := hne
  choose! cf hcf using hc

  have hadj' : ∀ u ∈ V, ∀ v ∈ V, ∀ ξ η : Wp, ⟪η, B u v ξ⟫_ℂ = ⟪B v u η, ξ⟫_ℂ := by
    intro u hu v hv ξ η
    rw [← hadj u hu v hv, ContinuousLinearMap.adjoint_inner_left]

  obtain ⟨u₀, hu₀, hl₀⟩ : ∃ u₀ ∈ V, l₀ u₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hne₁ (by rw [hcf v₁ hv₁ ξ₁ u₁ hu₁, h u₁ hu₁, smul_zero])
  have hnpos : 0 < ‖l₀ u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hl₀) 2
  have hN0 : ((‖l₀ u₀‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hself : ⟪l₀ u₀, l₀ u₀⟫_ℂ = ((‖l₀ u₀‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

  obtain ⟨lam, hcol⟩ : ∃ lam : ℂ, ∀ v ∈ V, ∀ ξ : Wp, cf v ξ = lam * ⟪l₀ v, ξ⟫_ℂ := by
    refine ⟨starRingEnd ℂ (cf u₀ (l₀ u₀)) / ((‖l₀ u₀‖ ^ 2 : ℝ) : ℂ), fun v hv ξ => ?_⟩
    have h := hadj' u₀ hu₀ v hv ξ (l₀ u₀)
    rw [hcf v hv ξ u₀ hu₀, hcf u₀ hu₀ (l₀ u₀) v hv, inner_smul_right, inner_smul_left, hself] at h
    rw [div_mul_eq_mul_div, eq_div_iff hN0, mul_comm (cf v ξ)]
    rw [mul_comm] at h
    exact h
  have hB : ∀ u ∈ V, ∀ v ∈ V, ∀ ξ : Wp, B u v ξ = (lam * ⟪l₀ v, ξ⟫_ℂ) • l₀ u := by
    intro u hu v hv ξ
    rw [hcf v hv ξ u hu, hcol v hv ξ]

  have hq := hpos u₀ hu₀ (l₀ u₀)
  have he : ⟪l₀ u₀, B u₀ u₀ (l₀ u₀)⟫_ℂ = lam * (((‖l₀ u₀‖ ^ 2) * (‖l₀ u₀‖ ^ 2) : ℝ) : ℂ) := by
    rw [hB u₀ hu₀ u₀ hu₀, inner_smul_right, hself]
    push_cast
    ring
  rw [he, Complex.re_mul_ofReal, Complex.im_mul_ofReal] at hq
  have hmm : 0 < ‖l₀ u₀‖ ^ 2 * ‖l₀ u₀‖ ^ 2 := mul_pos hnpos hnpos
  have him : lam.im = 0 := (mul_eq_zero.mp hq.2).resolve_right hmm.ne'
  have hre : 0 ≤ lam.re := by
    by_contra h
    push Not at h
    linarith [mul_neg_of_neg_of_pos h hmm, hq.1]
  have hlam0 : lam ≠ 0 := by
    intro h0
    apply hne₁
    rw [hB u₁ hu₁ v₁ hv₁ ξ₁, h0, zero_mul, zero_smul]
  have hrepos : 0 < lam.re := by
    refine lt_of_le_of_ne hre (fun h => hlam0 ?_)
    exact Complex.ext (by simpa using h.symm) (by simpa using him)

  refine ⟨((Real.sqrt lam.re : ℝ) : ℂ), ⟨u₀, hu₀, smul_ne_zero ?_ hl₀⟩, fun u hu v hv => ?_⟩
  · exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hrepos)
  have ht : starRingEnd ℂ ((Real.sqrt lam.re : ℝ) : ℂ) * ((Real.sqrt lam.re : ℝ) : ℂ) = lam := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hre]
    exact Complex.ext (by simp) (by simp [him])
  ext η
  rw [hB u hu v hv η, rankOneInnerOperator_apply, inner_smul_left, smul_smul]
  congr 1
  rw [mul_right_comm, ht]

theorem isBesselMapSm_smul {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ}
    {ψ : Mat k r → ℂ} {σ : Mat k r → (H →L[ℂ] H)} {π : Mat k r → (Wp →L[ℂ] Wp)} {l : H → Wp}
    (hl : IsBesselMapSm z ψ σ π l) (t : ℂ) : IsBesselMapSm z ψ σ π (fun u => t • l u) := by
  unfold Formalism.MainNotions.S.IsBesselMapSm Formalism.MainNotions.S.IsCWCont at *
  obtain ⟨hadd, hsm, heq, C, Ws, hWs, hb⟩ := hl
  refine ⟨?_, ?_, ?_, ‖t‖ * C, Ws, hWs, ?_⟩
  · intro v hv w hw
    show t • l (v + w) = t • l v + t • l w
    rw [hadd v hv w hw, smul_add]
  · intro c v hv
    show t • l (c • v) = c • (t • l v)
    rw [hsm c v hv, smul_comm]
  · intro h hh m hm v hv
    show t • l (σ (h * m) v) = ψ m • π h (t • l v)
    rw [heq h hh m hm v hv, map_smul, smul_comm]
  · intro v hv
    show ‖t • l v‖ ≤ _
    rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb v hv) (norm_nonneg t)

end GlobalTheory.SgInf.BeRankOne

theorem GlobalTheory.SgInf.exists_isEll_DD : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → IsSmoothVec σ w → MultOne z (psiGen k r z c) σ π → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → NonVan z (psiGen k r z c) σ π w μG ν → ∃ l : H → Wp, IsEll z (psiGen k r z c) π μS σ (DD σ w) l := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide hsm hM1 ν hq hNV
  obtain ⟨-, hU, -, -, hHG, -, -, hDec, -⟩ := id hStd
  obtain ⟨-, -, -, hHS, -⟩ := id hSide
  obtain ⟨hinv, -, hDV, -, hVsm⟩ := GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hU
  have hsmDD : ∀ v ∈ DD σ w, v ∈ smoothVecs (k := k) (r := r) σ :=
    fun v hv => (hVsm hsm).1 v (hDV hv)
  have hae := GlobalTheory.SgInf.WUnfold.ae_mem_GG hHG hHS hq

  have hne : ∃ u ∈ (DD σ w : Set H), ∃ v ∈ (DD σ w : Set H), ∃ ξ : Wp,
      be (psiGen k r z c) π μS σ u v ξ ≠ 0 := by
    by_contra hz
    push Not at hz
    obtain ⟨W, hWG, hWν, hWeq, hWfin, hWne, hWfix⟩ := hNV
    have hW0 : ∀ y ∈ GG k r, W y = 0 := by
      intro y hy
      rw [← hWfix y hy,
        (GlobalTheory.T.bessel_functional_standard_side k r σ w a μG d z c π μS hStd hSide ν hq W hWG hWν hWeq hWfin y hy).2,
        integral_eq_zero_of_ae, smul_zero]
      filter_upwards [hae] with g hg
      exact hz _ (mem_DD σ w hy) _ (mem_DD σ w hg) _
    apply hWne
    show (∫⁻ x, (‖W (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂ν) = 0
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hae] with x hx
    simp [hW0 _ hx]
  obtain ⟨u₁, hu₁, v₁, hv₁, ξ₁, hne₁⟩ := hne
  obtain ⟨l₀, hB₀, hl₀⟩ := GlobalTheory.T.exists_continuous_besselMap_smoothVectors k r σ w a μG d z c π μS hStd hSide hsm v₁ hv₁ ξ₁

  have hcol : ∀ v ∈ (DD σ w : Set H), ∀ ξ : Wp, ∃ b : ℂ, ∀ u ∈ (DD σ w : Set H),
      be (psiGen k r z c) π μS σ u v ξ = b • l₀ u := by
    intro v hv ξ
    obtain ⟨l, hB, hl⟩ := GlobalTheory.T.exists_continuous_besselMap_smoothVectors k r σ w a μG d z c π μS hStd hSide hsm v hv ξ
    obtain ⟨b, hb | hb⟩ := hM1 l l₀ hB hB₀
    · exact ⟨b, fun u hu => by rw [← hl u hu]; exact hb u (hsmDD u hu)⟩
    · have hb0 : b ≠ 0 := by
        rintro rfl
        apply hne₁
        rw [← hl₀ u₁ hu₁, hb u₁ (hsmDD u₁ hu₁), zero_smul]
      refine ⟨b⁻¹, fun u hu => ?_⟩
      rw [← hl u hu, hb u (hsmDD u hu), inv_smul_smul₀ hb0]
  obtain ⟨t, ⟨u₂, hu₂, hne₂⟩, hrk⟩ := GlobalTheory.SgInf.BeRankOne.exists_rankOne_of_hermitian_nonneg_operatorKernel (DD σ w : Set H)
    (be (psiGen k r z c) π μS σ) l₀ hcol
    (fun u hu v hv =>
      (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w : Set H) hinv hDec u hu v hv).2.2.1)
    (fun v hv ξ => by
      have h := GlobalTheory.T.norm_identity_besselCoefficient_quotient k r σ w a μG d z c π μS hStd hSide ν hq v hv v hv v hv ξ
      exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩)
    ⟨u₁, hu₁, v₁, hv₁, ξ₁, hne₁⟩
  refine ⟨fun u => t • l₀ u, ?_⟩
  unfold GlobalTheory.SgInf.IsEll
  exact ⟨GlobalTheory.SgInf.BeRankOne.isBesselMapSm_smul hB₀ t, ⟨u₂, hu₂, hne₂⟩, hrk⟩
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LocalSetupGap

theorem exists_seq {k : ℕ} (u : Fin k → ℝ) : ∃ U : ℕ → ℝ, ∀ i : Fin k, U (i.val + 1) = u i :=
  ⟨fun n => if h : n - 1 < k then u ⟨n - 1, h⟩ else 0, fun i => by simp⟩

theorem exists_setup (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Mt k r)} {R : (Fin (2 * r + k + 1) → ℤ) → Rep k r}
    (hN : Num k r lam u b bv ga h q0) (hF : IsFam lam q0 R) (hS : SideG k r z π u μW μN μG νq) {c : ℝ} (hc : 0 < c)
    (hd : ∀ (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG (PI.BesselPeriodGGP.eps48 k r) mu →
      ∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = c * fdegHC mu) :
    ∃ l : ∀ ν, (R ν).H → Wp,
      Setup lam u b bv ga h q0 z π μW μN μG νq R l (fun ν => c * fdegHC (fun a => lam a + (ν a : ℝ))) := by
  have hnum := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (h / 2) := hnum.1.2.2.2.2
  have hDG : ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 →
      (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) := by
    intro ν hν
    obtain ⟨hp, hds⟩ := hF ν hν
    exact ⟨hp, hds, h / 2, (hnum.2 ν hν).2.2.1, hok⟩
  have hex : ∀ ν : Fin (2 * r + k + 1) → ℤ,
      ∃ l : (R ν).H → Wp, n1 ν ≤ q0 → IsBeL (R ν) z π μW μN l := by
    intro ν
    by_cases hν : n1 ν ≤ q0
    · obtain ⟨l, hl⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r (PI.BesselPeriodGGP.eps48 k r)
        (fun a => lam a + (ν a : ℝ)) (h / 2) (R ν) Wp z π u μW μN μG νq (hDG ν hν)
        (hnum.2 ν hν).2.2.1 hok hS
      exact ⟨l, fun _ => hl⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' hν⟩
  choose l hl using hex
  refine ⟨l, ?_⟩
  unfold Setup SideFam
  refine ⟨hN, hF, hS, fun ν hν => ⟨hl ν hν, ?_, ?_⟩⟩
  · exact mul_pos hc (GlobalTheory.FamilyDegreeRatio.degree_ratios k r lam u b bv ga h q0 hN ν hν).1
  · intro w hw
    exact hd _ (R ν) (hDG ν hν) w hw

theorem exists_setup_both : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ τ w w' θ (W : LocW D.R.k D.R.rS), HypTT D w w' → 0 < θ → GoodW D τ w w' θ W → ∀ t ∈ GG D.R.k D.R.rS, (∀ n, n ∈ Nset D.R.k D.R.rS ↔ t * n * t⁻¹ ∈ Nset D.R.k D.R.rS) → (∀ z, inWb D.R.k D.R.rS z → (∀ h ∈ UWset D.R.k D.R.rS z, t * h = h * t) ∧ ∀ n ∈ Nset D.R.k D.R.rS, psi D.R.k D.R.rS z cStd n = psiS D z (t * n * t⁻¹)) → ∀ R : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Rep D.R.k D.R.rS, IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R → haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; ∃ (U U' : ℕ → ℝ) (l : ∀ ν, (R ν).H → W.Wp) (l' : ∀ ν, (R ν).H → W.Wq) (dg : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℝ), Setup (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z W.π W.μW (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l dg ∧ Setup (lamD D τ) U' (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z' W.π' W.μW' (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS'.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l' dg := by
  intro hH D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w w' θ W hTT hθ hW t ht hNt hzt R hR
  have := FiniteDimensional.complete ℂ W.Wp
  have := FiniteDimensional.complete ℂ W.Wq
  obtain ⟨U, hU⟩ := exists_seq (uS D w τ)
  obtain ⟨U', hU'⟩ := exists_seq (uS D w' τ)
  obtain ⟨hNum, -, -⟩ := GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w U hU
  obtain ⟨hNum', -, -⟩ := GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w' U' hU'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -⟩ := hZ.1
  obtain ⟨hπ, hπ', hzb, hzb', hT, hT', hμG, hμW, -, hμW', -, hμN, hνS, hνS'⟩ := hW
  have hTw : 0 < Tz D.R.k D.R.rS W.z := by
    rw [hT]
    unfold Tr
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hTT.2.2.1 : 0 < (D.mem w).A.T)
  have hTw' : 0 < Tz D.R.k D.R.rS W.z' := by
    rw [hT']
    unfold Tr
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hTT.2.2.2.1 : 0 < (D.mem w').A.T)
  have hNH : PI.BesselPeriodGGP.IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hμN]
    refine GlobalTheory.haarLie_isHaarOn_Nset _ _ _ ?_ ENNReal.ofReal_lt_top
    unfold kapN
    exact ENNReal.ofReal_pos.mpr (mul_pos (Real.rpow_pos_of_pos (by linarith) _) hθ)
  have hS1 : SideG D.R.k D.R.rS W.z W.π U W.μW W.μN W.μG W.νS :=
    ⟨hzb, hTw, ⟨_, hπ⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ U _ _ hzb hTw hπ hU, hμW, hNH, hμG, hνS⟩
  have hS2 : SideG D.R.k D.R.rS W.z' W.π' U' W.μW' W.μN W.μG W.νS' :=
    ⟨hzb', hTw', ⟨_, hπ'⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ U' _ _ hzb' hTw' hπ' hU', hμW', hNH, hμG,
      hνS'⟩
  have hM1 := (GlobalTheory.BesselMoveGap.bessel_move_gap hH D.R.k D.R.rS W.Wp W.z W.π U
    ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.μW W.μN W.μG W.νS t ht hNt
    (hzt W.z hzb).1 (hzt W.z hzb).2 hS1).1
  have hM2 := (GlobalTheory.BesselMoveGap.bessel_move_gap hH D.R.k D.R.rS W.Wq W.z' W.π' U'
    ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.μW' W.μN W.μG W.νS' t ht hNt
    (hzt W.z' hzb').1 (hzt W.z' hzb').2 hS2).1
  obtain ⟨c, hc, hsch⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hH.1 D.R.k D.R.rS
    (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) W.μG hμG
  obtain ⟨l, hl⟩ := exists_setup hH hNum hR hM1 hc (fun mu Q h => (hsch mu Q h).1)
  obtain ⟨l', hl'⟩ := exists_setup hH hNum' hR hM2 hc (fun mu Q h => (hsch mu Q h).1)
  exact ⟨U, U', l, l', _, hl, hl'⟩

end GlobalTheory.Amp.LocalSetupGap
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselSchurGap

theorem schur_fdeg_gap : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μG : Measure (Formalism.QuantumDeterminants.Mt k r)),
    PI.BesselPeriodGGP.IsHaarOn (GG k r) μG → ∃ c : ℝ, 0 < c ∧ ∀ (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r),
    R.IsDG ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = c * Formalism.QuantumDeterminants.fdegHC mu) ∧
    ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r =>
      ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG =
        ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
  intro hy k r ε μG hμ
  have hHC : HCFdegG := hy.2.2.2.2.2.2
  by_cases hQ : ∃ Q, PI.UpqRep.IsCayleyU k r ε Q
  swap
  · refine ⟨1, one_pos, fun mu R hR => absurd ?_ hQ⟩
    obtain ⟨Q, hQ, -⟩ := hR.2
    exact ⟨Q, hQ⟩
  obtain ⟨c, hc, hF⟩ := hHC k r ε hQ
  obtain ⟨Q, hQ⟩ := hQ
  have hP : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1.1
  have hH : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r := hQ.1.2
  obtain ⟨a, ha0, hat, ha⟩ := GlobalTheory.BesselDegree.haar_eq_smul hP hH μG hμ
  have hapos : 0 < a.toReal := ENNReal.toReal_pos ha0 hat
  have hme : MeasurableEmbedding (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε Q) :=
    (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_closedEmbedding (ε := ε) Formalism.REAL.isClosedEmbeddingMatrix hP).measurableEmbedding
  refine ⟨c / a.toReal, div_pos hc hapos, fun mu R hR => ?_⟩
  have hDS := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R (GlobalTheory.isDS_of_isDG hR) Q hQ
  obtain ⟨hd, hS⟩ := hF mu R.H _ hR.gap hR.hc hDS
  have hd' : 0 < c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu := by
    rw [div_mul_eq_mul_div]; exact div_pos hd hapos
  have key : ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r =>
      ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG =
        ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
    intro v w v' w'
    obtain ⟨h1, h2⟩ := hS v w v' w'
    rw [ha]
    constructor
    · refine Integrable.smul_measure ?_ hat
      rw [hme.integrable_map_iff]
      exact h1
    · rw [integral_smul_measure, hme.integral_map]
      have h3 : ∫ g, ⟪w, R.σ (Matrix.of (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε Q g)) v⟫_ℂ *
          star ⟪w', R.σ (Matrix.of (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε Q g)) v'⟫_ℂ
          ∂(Formalism.REAL.muG ε) = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := h2
      rw [h3, div_mul_eq_mul_div, Complex.ofReal_div, div_div_eq_mul_div, Complex.real_smul]
      ring
  exact ⟨fun w hw => Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq hd' key hw, key⟩

theorem exists_mass_eq (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ} {c : ℂ}
    {μW μN μG νq : Measure (Mt k r)} {B : R.H → Wp} {w : R.H} (hc : c ≠ 0) (hDS : R.IsDS ε mu)
    (hgap : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hS : SideG k r z π u μW μN μG νq)
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B) (hw : R.KFin w)
    (h0 : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ 0)
    (h1 : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ ⊤) :
    ∃ a : ℝ≥0∞, ∀ v ∈ R.sm, PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) = a * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  have hDG : R.IsDG ε mu := ⟨hDS.1, hDS.2, h, hgap, hok⟩
  obtain ⟨t, htG, htN, htz, -⟩ := GlobalTheory.TorusScale.exists_torus_scale k r c hc
  obtain ⟨-, htW, htψ⟩ := htz z hS.1
  obtain ⟨hS', hR⟩ := GlobalTheory.T.isBesselMap_conj_iff_and_besselFn_eq_rankOne hH k r Wp z π u c μW μN μG νq t htG htN htW htψ hS
  obtain ⟨hmul, hone, hinn, hsm, hTK, -, hKT, -, hcont⟩ :=
    GlobalTheory.rep_basic_of_isDS hH.1.1.2.2.1 k r ε mu R hDS
  have hU : Formalism.MainNotions.S.IsURepOn (BranchingSupport.GG k r) R.σ := by
    refine ⟨⟨?_, ?_⟩, fun g hg v => ?_, hcont⟩
    · ext v; simpa using hone v
    · intro a ha b hb; ext v; simpa using hmul a ha b hb v
    · have := hinn g hg v v
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
      have h2 : ‖R.σ g v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast this
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hB' := ((hR R hU).1 B).1 hB
  obtain ⟨htu, htinv, -⟩ := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r t htG
  have hdet : IsUnit t.det := (Matrix.isUnit_iff_isUnit_det t).mp htu
  have hae : ∀ {μN νq : Measure (Mt k r)}, SideG k r z π u μW μN μG νq →
      ∀ᵐ x ∂νq, Matrix.of x ∈ UH (Hpk k r) := fun hS => by
    obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hS
    obtain ⟨hS0, hS1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
    exact Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hS0 hS1 hq
  have hmove : ∀ v, PI.BesselPeriodGGP.l2SG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j)
      (fun g => B (R.σ t (R.σ g v))) = PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) := fun v => by
    unfold PI.BesselPeriodGGP.l2SG
    rw [(GlobalTheory.BesselSchur.measurableEmbedding_lmul hdet).lintegral_map]
    refine lintegral_congr_ae ?_
    filter_upwards [hae hS] with x hx
    have e : R.σ t (R.σ (t⁻¹ * Matrix.of x) v) = R.σ (Matrix.of x) v := by
      rw [← hmul t htG _ (Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul htinv hx), ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
        Matrix.one_mul]
    exact congrArg (fun y => ((‖B y‖₊ : ℝ≥0∞)) ^ 2) e
  obtain ⟨l, hl⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r ε mu h R Wp z π u _ _ _ _ hDG hgap hok hS'
  obtain ⟨v₁, hv₁, hlv⟩ := GlobalTheory.T.exists_kFinite_besselPeriod_ne_zero_gap hH k r ε mu h R Wp z π u _ _ _ _ _ l w hDS hgap hok hS' hB' hw
    (by rw [hmove]; exact h0) (by rw [hmove]; exact h1) hl
  obtain ⟨c₀, hc₀, hfd⟩ := schur_fdeg_gap hH.1 k r ε μG hS.2.2.2.2.2.2.1
  have hdd : 0 < c₀ * Formalism.QuantumDeterminants.fdegHC mu := mul_pos hc₀ (GlobalTheory.BesselSchur.fdegHC_pos hDS.1.1)
  have hv₁s : v₁ ∈ R.sm := hTK _ (hKT _ hv₁)
  have hiso := Gp91.GlobalTheory.T.isIsoB_sqrt_fdeg_smul_of_gap hH.1 k r ε mu h R Wp z π u _ _ _ _ l _ hDG hgap hok hS' hl
    (hfd mu R hDG).1 ⟨v₁, hv₁s, hlv⟩
  obtain ⟨hb, hiso⟩ := hiso
  obtain ⟨a, ha⟩ := GlobalTheory.T.besselMaps_proportional_discreteSeries_largeGap hH k r ε mu R Wp z π u _ _ _ _ _ _ hDG hS' hb
    ⟨v₁, hv₁s, smul_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hdd).ne') hlv⟩ hB'
  refine ⟨(‖a‖₊ : ℝ≥0∞) ^ 2, fun v hv => ?_⟩
  have e : ((‖v‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]; rfl
  rw [← hmove, e, ← hiso v hv]
  unfold PI.BesselPeriodGGP.l2SG
  rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
  refine lintegral_congr_ae ?_
  filter_upwards [hae hS'] with x hx
  rw [ha _ (hsm _ hx v hv), nnnorm_smul, ENNReal.coe_mul, mul_pow]

theorem bessel_schur : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), 1000 ≤ Cl →
    (∀ τ w w' θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W → 0 < θ) → (∀ w, 0 < Tr D w) →
    BSch D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hH D large₂ C' Cl Cg cb Cu cT CT C0 hCl hθ _ hZ τ w w' θ W hW A hA hT v hv
  have hθ0 := hθ τ w w' θ W hW
  have := FiniteDimensional.complete ℂ W.Wp
  have hU : ∀ i : Fin D.R.k, uOne D w τ (i.val + 1) = uS D w τ i := fun i => by
    unfold uOne
    rw [dite_eq_left ⟨by omega, i.isLt⟩]
    rfl
  obtain ⟨hnum, -, heps⟩ := GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w _ hU
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgap, hok, -, hh, -⟩ := hnum
  rw [heps] at hgap
  have hgap' : GapAtLeast (epsSH D.R) (lamD D τ) ((D.R.r : ℝ) ^ 19 / 4) := fun a b hab =>
    le_trans (by have : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
                 linarith) (hgap a b hab)
  have hv1 : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvpos : 0 < D.host.v := by linarith
  obtain ⟨c1, -, z1, -, t1, -, hG, w1, -, -, -, hN, q1, -⟩ := hW
  obtain ⟨hpar, hds, b1, -, hsm, hv0, ⟨P, hP, hlow⟩, hc, l1, -, -⟩ := hA
  have hTz : 0 < Tz D.R.k D.R.rS W.z := by rw [t1]; exact hT
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hN]
    exact GlobalTheory.haarLie_isHaarOn_Nset _ _ _ (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_lt_top
  have hS : SideG D.R.k D.R.rS W.z W.π (uOne D w τ) W.μW W.μN W.μG W.νS :=
    ⟨z1, hTz, ⟨_, c1⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ _ _ _ z1 hTz c1 hU, w1, hNH, hG, q1⟩
  have hka : 0 < D.host.ka := div_pos Real.pi_pos hvpos
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  have hcne : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by positivity)
  have hKF : (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin A.v0 := by
    obtain ⟨S, ⟨hfd, hst⟩, hwS⟩ := PI.UnitaryGroupMassFormula.LowSmooth.exists_finStable_of_mem_sSup (Formalism.REAL.Kset (epsSH D.R))
      (fun g => A.σ (P⁻¹ * g * P))
      (F := {S | IsKTypeOf (epsSH D.R) (fun g => A.σ (P⁻¹ * g * P)) (lowK (epsSH D.R) (lamD D τ)) S})
      (fun S hS => ⟨hS.1, hS.2.1⟩) hlow
    refine ⟨S, hfd, hwS, fun g hg x hx => ?_⟩
    obtain ⟨hK, hback⟩ := PI.UnitaryGroupMassFormula.LowSmooth.conj_mem_Kset hP hg
    have h := hst _ hK x hx
    simp only at h
    rwa [hback] at h
  have hnt : Nontrivial W.Wp := by
    obtain ⟨g, -, hnt, -⟩ := c1
    exact hnt
  have hrk : (0 : ℝ) < Module.finrank ℂ W.Wp := by exact_mod_cast Module.finrank_pos
  have l1' : PI.BesselPeriodGGP.l2SG W.νS (fun g => A.B (A.σ g A.v0)) =
      ENNReal.ofReal (A.cN * Module.finrank ℂ W.Wp) := l1
  obtain ⟨a, ha⟩ := exists_mass_eq hH (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) (B := A.B) (w := A.v0) hcne ⟨hpar, hds⟩
    hgap' hok hS (GlobalTheory.BesselSchur.isBesselMapSm_of b1) hKF
    (by rw [l1']; exact (ENNReal.ofReal_pos.2 (mul_pos hc hrk)).ne') (by rw [l1']; exact ENNReal.ofReal_ne_top)
  have e1 : l2SG W.νS (fun g => A.B (A.σ g v)) = a * (‖v‖₊ : ℝ≥0∞) ^ 2 := ha v hv
  have e2 : l2SG W.νS A.Φ = a * (‖A.v0‖₊ : ℝ≥0∞) ^ 2 := ha A.v0 hsm
  rw [e1, e2]
  ring

end GlobalTheory.BesselSchurGap
end
