module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLintegralEqOfMeasurable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle282
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle139
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle119
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle285
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle252
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDual
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle221
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle124
import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiffQuotientBesselMapTendsto
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle284
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle238
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.IwasawaShape

theorem gauge_ne_zero_finite {n : ℕ} {ε : Fin n → Bool} (M : Subgroup (Formalism.REAL.UJ ε)) (d : ℕ)
    (μ : Measure (Formalism.REAL.UJ ε)) (hM : IsClosed (M : Set (Formalism.REAL.UJ ε)))
    (hμ : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) d μ) : μ ≠ 0 ∧ IsFiniteMeasureOnCompacts μ := by
  obtain ⟨h0, hinv, hlim⟩ := hμ
  have hL0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hLt : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hpos : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hr0, hrt⟩ := (hpos.and ((hlim.eventually_ne hL0).and (hlim.eventually_ne hLt))).exists
  set B : Set (Formalism.REAL.UJ ε) := {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} with hB
  have hden0 : ENNReal.ofReal (r ^ d) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact pow_pos hr d
  have hB0 : μ B ≠ 0 := by
    intro h; apply hr0; rw [h, ENNReal.zero_div]
  have hBt : μ B ≠ ⊤ := by
    intro h; apply hrt; rw [h]; exact ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top
  have hf : Continuous fun g : Formalism.REAL.UJ ε => Real.sqrt (Formalism.REAL.hs (uMat g - 1)) := by
    refine Real.continuous_sqrt.comp ?_
    unfold Formalism.REAL.hs
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun k _ => ?_
    refine (Continuous.norm ?_).pow 2
    exact (continuous_apply k).comp ((continuous_apply i).comp
      (GlobalTheory.FlagLeviGroup.continuous_uMat.sub continuous_const))
  have hBm : MeasurableSet B := (isClosed_le hf continuous_const).measurableSet
  have hBn : B ∈ nhds (1 : Formalism.REAL.UJ ε) := by
    have hO : IsOpen {g : Formalism.REAL.UJ ε | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < r} :=
      isOpen_lt hf continuous_const
    refine Filter.mem_of_superset (hO.mem_nhds ?_) fun g hg => by
      rw [hB, Set.mem_ofPred_eq]; rw [Set.mem_ofPred_eq] at hg; exact hg.le
    show Real.sqrt (Formalism.REAL.hs (uMat (1 : Formalism.REAL.UJ ε) - 1)) < r
    rw [GlobalTheory.FlagLeviGroup.uMat_one, sub_self]
    unfold Formalism.REAL.hs
    simpa using hr
  refine ⟨fun h => hB0 (by rw [h]; rfl), ?_⟩
  exact finiteOnCompacts_of_nhds M μ h0 hM (fun s hs => hinv s hs) B hBm hBn hBt

theorem coe_KG {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.KG ε : Set (Formalism.REAL.UJ ε)) = maxK ε := by
  ext g
  have hJ := GlobalTheory.RealIwasawa.uMat_form g
  change g ∈ Formalism.REAL.KG ε ↔ (uMat g)ᴴ * uMat g = 1
  rw [Formalism.REAL.mem_KG]
  change (uMat g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g) ↔ _
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  have h' : uMat g * (uMat g)ᴴ = 1 := mul_eq_one_comm.mp h
  calc uMat g * Formalism.REAL.Jm ε = uMat g * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by rw [hJ]
    _ = (uMat g * (uMat g)ᴴ) * Formalism.REAL.Jm ε * uMat g := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε * uMat g := by rw [h', Matrix.one_mul]

theorem iwasawa_shape : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (μN μM μK : Measure (Formalism.REAL.UJ ε)), IsGaugeSub (flagN ε W) (dimN n j) μN → IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM → μK (maxK ε)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ maxK ε, μK.map (fun g => k * g) = μK) → ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ φ : Formalism.REAL.UJ ε → ENNReal, Measurable φ → ∫⁻ g, φ g ∂(Formalism.REAL.muG ε) = κ * ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) * ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN := by
  intro n ε p q _ _ a j hj W hW μN μM μK hN hM hK0 hK1 hKi
  obtain ⟨⟨N, hNs⟩, hNc, -⟩ := GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε a j W hW
  obtain ⟨⟨M, hMs⟩, hMc, ⟨K, hKs⟩, -, hnorm⟩ := GlobalTheory.FlagLeviGroup.levi_compact_subgroups n ε a W
  obtain ⟨hdec, huniq⟩ := GlobalTheory.RealIwasawa.iwasawa n ε a j W hW
  have eN : ∀ x, x ∈ N ↔ x ∈ flagN ε W := fun x => by rw [← hNs]; rfl
  have eM : ∀ x, x ∈ M ↔ x ∈ flagM ε W := fun x => by rw [← hMs]; rfl
  have eK : ∀ x, x ∈ K ↔ x ∈ maxK ε := fun x => by rw [← hKs]; rfl
  have hKc : IsCompact (K : Set (Formalism.REAL.UJ ε)) := by
    rw [hKs, ← coe_KG]
    exact isCompact_iff_compactSpace.mpr (Formalism.REAL.instCompactKG n ε)
  have hN' : IsGaugeSub (N : Set (Formalism.REAL.UJ ε)) (dimN n j) μN := by rw [hNs]; exact hN
  have hM' : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM := by
    rw [hMs]; exact hM
  have hNc' : IsClosed (N : Set (Formalism.REAL.UJ ε)) := by rw [hNs]; exact hNc
  have hMc' : IsClosed (M : Set (Formalism.REAL.UJ ε)) := by rw [hMs]; exact hMc
  obtain ⟨hN0, hNf⟩ := gauge_ne_zero_finite N _ μN hNc' hN'
  obtain ⟨hM0, hMf⟩ := gauge_ne_zero_finite M _ μM hMc' hM'
  have := hNf
  have := hMf
  have : IsProbabilityMeasure μK := ⟨hK1⟩
  have : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  have hmod := GlobalTheory.T.isotropicFlag_levi_conj_haar_modulus n ε a j W hj hW μN hN
  obtain ⟨c, hc0, hct, hc⟩ := GlobalTheory.IwasawaShape.exists_lintegral_eq N M K hNc' hMc' hKc
    (fun m hm u hu => (eN _).2 (hnorm m ((eM m).1 hm) u ((eN u).1 hu)))
    (fun u hu m hm hk => huniq u ((eN u).1 hu) m ((eM m).1 hm) ((eK _).1 hk))
    (fun g => by
      obtain ⟨u, hu, m, hm, k, hk, rfl⟩ := hdec g
      exact ⟨u, (eN u).2 hu, m, (eM m).2 hm, k, (eK k).2 hk, rfl⟩)
    (Formalism.REAL.muG ε) μN μM μK (NeZero.ne _) hN0 hM0 hN'.1 hM'.1
    (fun s hs => hN'.2.1 s hs) (fun s hs => hM'.2.1 s hs) (fun s hs => hKi s ((eK s).1 hs))
    (fun m => ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id))
    (fun m hm => hmod m ((eM m).1 hm))
  exact ⟨c, hc0, hct, hc⟩

end GlobalTheory.IwasawaShape
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.fibreVolume_twoFlags_generalPosition : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r) (De s : ℝ) (μR : Measure (Mt k r)), 1 ≤ r → 2 * r + 6 ≤ k → TwoFl k r z z' γ → DeOK k r z z' γ De → 0 < s → NormR k r γ s μR → ∀ g₁ ∈ GG k r, lebN k r {n | Yv k r z z' γ (Matrix.of n * g₁) = 0} = 0 ∧ ∀ φ, SubCut (GG k r) μR φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ (rmulM g₁ n) * (Eset k r z z' γ R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol k r R₀ De y / s) := by
  first | exact @GlobalTheory.Amp.FibreVolumeGen.fibre_volume | exact GlobalTheory.Amp.FibreVolumeGen.fibre_volume | (intros; apply GlobalTheory.Amp.FibreVolumeGen.fibre_volume <;> assumption)
end

section

namespace GlobalTheory.ThA

open Formalism.FourierDecayAlt MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem exists_isStdOf (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hk : 1 ≤ k) (hsec : IsSection k r L.z L.z' μsec) :
    ∃ Bs : B.RealPlaceData k r L.Wp L.Wq, IsStdOf L μsec Bs := by
  obtain ⟨μG, hμG⟩ := P.unitary_group_haar_exists k r
  obtain ⟨χ, hχs, hχsupp, hχint⟩ := P.character_exists_alt
  have h1 := GlobalTheory.T.hcTypeW_continuous_unitary_irreducible k r L.z L.u L.Wp L.π L.hz.1 L.hz.2 L.hπ
  have h1' := GlobalTheory.T.hcTypeW_continuous_unitary_irreducible k r L.z' L.u' L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ'
  have hW := GlobalTheory.T.isTwoSidedHaar_of_leftInvariant_probability_compactUnitary k r L.z L.μW L.hz.1 L.hz.2 L.hμW.1 L.hμW.2
  have hW' := GlobalTheory.T.isTwoSidedHaar_of_leftInvariant_probability_compactUnitary k r L.z' L.μW' L.hz'.1 L.hz'.2 L.hμW'.1 L.hμW'.2
  have hN := P.Dx2.MN.haar (k := k) r
  exact ⟨⟨L.z, L.z', L.π, L.π', μG, L.μW, D.muN k r, L.μW', μsec, χ, hk, L.hz.1, L.hz'.1, L.hz.2, L.hz'.2,
    h1.2.1, h1'.2.1, h1.2.2.2.1, h1'.2.2.2.1, h1.2.2.1, h1'.2.2.1, hμG, hW, hN, hW', hsec, hχs, hχsupp, hχint⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end GlobalTheory.ThA
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.DeepCover

theorem isIsot_span (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (h0 : R ≠ ⊥)
    (h : R ≤ perpIn I x R) : I.IsIsot (Submodule.span I.E (R : Set (Fin I.n → I.E))) := by
  have hspan : Submodule.span I.E (R : Set (Fin I.n → I.E)) ≤
      Submodule.span I.E (perpIn I x R : Set (Fin I.n → I.E)) :=
    Submodule.span_mono h

  have h1 : ∀ s ∈ R, ∀ y ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)),
      Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 :=
    fun s hs y hy => GlobalTheory.FlagIso.hform_span I x R (hspan hy) hs

  have h2 : ∀ y ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)),
      ∀ z ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)),
        Formalism.UG.hform (starRingEnd I.E) I.J y z = 0 := by
    intro y hy z hz
    have hker : Submodule.span I.E (R : Set (Fin I.n → I.E)) ≤
        LinearMap.ker (GlobalTheory.FlagIso.hR I.J y) := by
      rw [Submodule.span_le]
      intro s hs
      rw [SetLike.mem_coe, LinearMap.mem_ker, GlobalTheory.FlagIso.hR_apply,
        ← GlobalTheory.FlagIso.hform_star I.J I.J_herm s y, h1 s hs y hy, star_zero]
    have hz' := hker hz
    rwa [LinearMap.mem_ker, GlobalTheory.FlagIso.hR_apply] at hz'
  refine ⟨?_, h2⟩
  intro hbot
  apply h0
  rw [eq_bot_iff]
  intro r hr
  have hr' : r ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)) := Submodule.subset_span hr
  rw [hbot] at hr'
  exact (Submodule.mem_bot _).2 ((Submodule.mem_bot _).1 hr')

theorem unipotent_orbit_cover : ∀ (I : AutInst) (x : I.GA) (g q : ℕ), 1 ≤ g → 1 ≤ I.n → (∀ v, rkR (I.ε v) ≤ q) → least I x < 1 / 2 → ∃ W : Submodule I.E (Fin I.n → I.E), I.IsIsot W ∧ ∀ ν : I.Ginf, ((ν, 1) : I.GA) ∈ I.NA W → ∃ γ ∈ I.GFset, ∃ k ∈ I.Kg g, ∃ y ∈ omega I x W ((I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * (2 * least I x) ^ ((1 : ℝ) / q) / 4), ((ν, 1) : I.GA) * x = γ * y * (1, k) := by
  intro I x g q hg hn hq hlt

  obtain ⟨⟨a, S, τ, hF⟩, -, hspec⟩ := GlobalTheory.PointFlag.flag_spec I x
  obtain ⟨hpieces, hzero⟩ := hspec a S τ hF
  obtain ⟨ha0, hτ0⟩ := hzero hn
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exact absurd (ha0.1 h) (not_le.2 hlt)
    · exact h
  obtain ⟨hall, -, -, hstep⟩ := GlobalTheory.T.smallSizeCanonicalFlag_pieces_properties I x a S τ hF
  obtain ⟨-, -, hSlast, hτmono, hτ, -⟩ := hF

  obtain ⟨τ', hτ'⟩ : ∃ f : ℕ → ℝ, f = fun i => if h : i < a then τ ⟨i, h⟩ else 1 / 2 := ⟨_, rfl⟩
  have hτ'lt : ∀ i (h : i < a), τ' i = τ ⟨i, h⟩ := by
    intro i h; rw [hτ']; exact dif_pos h
  have hτ'ge : ∀ i, a ≤ i → τ' i = 1 / 2 := by
    intro i h; rw [hτ']; exact dif_neg (not_lt.2 h)
  have hpos : ∀ i ≤ a, 0 < τ' i := by
    intro i _
    rcases lt_or_ge i a with h | h
    · rw [hτ'lt i h]; exact (hτ ⟨i, h⟩).1
    · rw [hτ'ge i h]; norm_num
  have hinc : ∀ i < a, τ' i < τ' (i + 1) := by
    intro i hi
    rw [hτ'lt i hi]
    rcases lt_or_ge (i + 1) a with h | h
    · rw [hτ'lt (i + 1) h]
      exact hτmono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
    · rw [hτ'ge (i + 1) h]; exact (hτ ⟨i, hi⟩).2.1
  have hlast : τ' a = 1 / 2 := hτ'ge a le_rfl

  have hrk : ∀ i (hi : i ≤ a), i ≤ rkK (S ⟨i, Nat.lt_succ_of_le hi⟩) := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have h1 := ih (Nat.le_of_succ_le hk)
      have h2 : rkK (S (Fin.castSucc ⟨k, hk⟩)) < rkK (S (Fin.succ ⟨k, hk⟩)) :=
        ((hpieces ⟨k, hk⟩).2.1)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt h1 h2)
  obtain ⟨-, hrkR, -⟩ := GlobalTheory.FlagIso.flag_isotropic I x
  have haq : a ≤ q := by
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    have h1 : a ≤ rkK (S (Fin.last a)) := hrk a le_rfl
    rw [hSlast] at h1
    exact h1.trans ((hrkR v).trans (hq v))

  obtain ⟨b, hb, hratio, hsq⟩ := GlobalTheory.exists_consecutive_ratio_le_rpow a q τ' ha haq hpos hinc hlast
  rw [hτ'lt 0 ha, hτ0 ha, hτ'lt b hb] at hratio hsq
  have hi_pos : 0 < τ ⟨b, hb⟩ := (hτ ⟨b, hb⟩).1
  have hlo_pos : 0 < τ' (b + 1) := hpos (b + 1) hb
  obtain ⟨-, -, -, hne, hlarge, hgeL⟩ := hstep ⟨b, hb⟩
  have hRperp : S (Fin.succ ⟨b, hb⟩) ≤ perpIn I x (S (Fin.succ ⟨b, hb⟩)) :=
    le_trans (hall _).2.2.1 (hall _).2.2.2.1
  have hsat : IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (S (Fin.succ ⟨b, hb⟩)) :=
    (hall _).1
  have hlo : ∀ N, S (Fin.succ ⟨b, hb⟩) < N → N ≤ lamX I x →
      τ' (b + 1) ≤ sizeQ (bas I) (frm I x) N (S (Fin.succ ⟨b, hb⟩)) := by
    rw [hτ']; exact hgeL
  refine ⟨Submodule.span I.E (S (Fin.succ ⟨b, hb⟩) : Set (Fin I.n → I.E)),
    isIsot_span I x _ hne hRperp, ?_⟩
  intro ν hν
  obtain ⟨γ, ⟨hγF, -⟩, hk, A, Z, hAZ, heq, hbound, hst⟩ :=
    GlobalTheory.T.small_fundamental_set_real_unipotent I x g (S (Fin.succ ⟨b, hb⟩)) (τ' (b + 1)) (τ ⟨b, hb⟩)
      ((2 * least I x) ^ ((1 : ℝ) / q)) hg hsat hne hRperp hi_pos hlarge hlo
      ((div_le_iff₀ hlo_pos).1 hratio) hsq ν hν

  obtain ⟨m, -, hm⟩ := hst 1 1
  have hm' : ∀ v, uMat (m v) * uMat (x.1 v) =
      uMat (x.1 v) * NormedSpace.exp (A v) * NormedSpace.exp (Z v) := by
    intro v; simpa only [Complex.ofReal_one, one_smul] using hm v

  obtain ⟨-, -, -, -, -, -, hKg⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨-, ⟨K, hK⟩, -⟩ := hKg g hg
  have hkinv : ((x⁻¹ * γ * x).2)⁻¹ ∈ I.Kg g := by
    rw [← hK] at hk ⊢
    exact K.inv_mem hk
  refine ⟨γ, hγF, ((x⁻¹ * γ * x).2)⁻¹, hkinv, ((m * x.1 : I.Ginf), x.2), ?_, ?_⟩
  · refine ⟨rfl, A, Z, hAZ, hbound, fun v => ?_, hst⟩
    show uMat (m v) * uMat (x.1 v) = _
    exact hm' v
  · have key : ∀ v, uMat (ν v) * uMat (x.1 v) = uMat (γ.1 v) * (uMat (m v) * uMat (x.1 v)) := by
      intro v
      rw [heq v, hm' v]
      simp only [mul_assoc]
    refine Prod.ext ?_ ?_
    · show ν * x.1 = γ.1 * (m * x.1) * 1
      rw [mul_one]
      funext v
      exact Subtype.ext (Units.ext (key v))
    · show 1 * x.2 = γ.2 * x.2 * ((x⁻¹ * γ * x).2)⁻¹
      simp only [Prod.snd_mul, Prod.snd_inv]
      group

end GlobalTheory.DeepCover
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

namespace GlobalTheory.UnitaryVolume

theorem Jm_allPos (N : ℕ) : Formalism.REAL.Jm (allPos N) = 1 := by
  simp [Formalism.REAL.Jm, allPos]

theorem mul_conjTranspose_self {N : ℕ} (g : Formalism.REAL.UJ (allPos N)) : uMat g * (uMat g)ᴴ = 1 := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm (allPos N) * uMat g = Formalism.REAL.Jm (allPos N) := g.2
  rw [Jm_allPos, Matrix.mul_one] at h
  exact mul_eq_one_comm.1 h

theorem row_norm {N : ℕ} (g : Formalism.REAL.UJ (allPos N)) (i : Fin N) : ∑ k, ‖uMat g i k‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (mul_conjTranspose_self g) i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h2 : ((∑ k, ‖uMat g i k‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (Complex.mul_conj' _).symm
  exact_mod_cast h2

theorem muG_univ_lt_top (N : ℕ) : Formalism.REAL.muG (allPos N) Set.univ < ⊤ := by
  have h := Formalism.REAL.ballFinite N (allPos N) N
  have e : {g : Formalism.REAL.UJ (allPos N) | Formalism.REAL.hsG g ≤ (N : ℝ)} = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    change ∑ i, ∑ k, ‖uMat g i k‖ ^ 2 ≤ (N : ℝ)
    simp [row_norm]
  rwa [e] at h

theorem muG_univ_ne_zero (N : ℕ) : Formalism.REAL.muG (allPos N) Set.univ ≠ 0 :=
  (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'

theorem gauss_inv_single {n : ℕ} (g : Formalism.REAL.UJ (allPos (n + 1))) :
    gauss ((uMat g)⁻¹ *ᵥ (Pi.single 0 1 : Fin (n + 1) → ℂ)) = Real.exp (-1) := by
  rw [Matrix.inv_eq_right_inv (mul_conjTranspose_self g), gauss]
  congr 2
  rw [← row_norm g 0]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mulVec_single_one, Matrix.conjTranspose_apply]

theorem volU_succ (n : ℕ) :
    volU (n + 1) = volU n * (2 ^ (n + 1) * Real.pi ^ (n + 1) / (n.factorial : ℝ)) := by
  have h : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
    rw [← Nat.choose_two_right, ← Nat.choose_two_right, Nat.choose_succ_succ' n 1]
    simp [add_comm]
  unfold volU sphV
  rw [Finset.prod_Icc_succ_top (by omega), h]
  simp only [Nat.add_sub_cancel]
  ring

theorem volU_pos (n : ℕ) : 0 < volU n := by
  unfold volU sphV
  have := Real.pi_pos
  exact mul_pos (Finset.prod_pos fun l _ => by positivity) (by positivity)

theorem volume_zero (c : ℝ) (hc : IsGauge (allPos 0) c) :
    c * (Formalism.REAL.muG (allPos 0) Set.univ).toReal = volU 0 := by
  have h1 : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (0 ^ 2))) 1)).toReal = 1 := by
    change (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1)).toReal = 1
    have e : Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1 = Set.univ :=
      Set.eq_univ_of_forall fun x => by rw [Subsingleton.elim x 0]; simp
    rw [e, ← (PiLp.volume_preserving_toLp (Fin 0)).measure_preimage MeasurableSet.univ.nullMeasurableSet]
    simp [volume_pi, Measure.pi_univ]
  unfold IsGauge at hc
  rw [h1] at hc
  have h2 : Filter.Tendsto (fun _ : ℝ => c * (Formalism.REAL.muG (allPos 0) Set.univ).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have e : {g : Formalism.REAL.UJ (allPos 0) | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} = Set.univ :=
      Set.eq_univ_of_forall fun g => by
        simpa [Formalism.REAL.hs] using le_of_lt hr
    rw [e]
    simp
  rw [tendsto_const_nhds_iff.1 h2]
  simp [volU, sphV]

theorem volume_unitary : ∀ (N : ℕ) (c : ℝ), IsGauge (allPos N) c →
    c * (Formalism.REAL.muG (allPos N) Set.univ).toReal = volU N := by
  intro N
  induction N with
  | zero => exact volume_zero
  | succ n ih =>
    intro c hc
    obtain ⟨c₀, hc₀, -, hu⟩ := GlobalTheory.GaugeConst.gauge_exists_pos_unique (n + 1) (allPos (n + 1))
    have hcpos : 0 < c := by rw [hu c hc]; exact hc₀
    obtain ⟨c', hc'pos, hc', -⟩ := GlobalTheory.GaugeConst.gauge_exists_pos_unique n (allPos n)
    have hv := ih c' hc'
    let x₀ : Fin (n + 1) → ℂ := Pi.single 0 1
    let B : Matrix (Fin (n + 1)) (Fin n) ℂ := (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix id Fin.succ
    have hq : qEps (allPos (n + 1)) x₀ = sgn ℝ true := by
      simp [qEps, sgn, allPos, x₀, Fin.sum_univ_succ]
    have hx : star x₀ ᵥ* (Formalism.REAL.Jm (allPos (n + 1)) * B) = 0 := by
      rw [Jm_allPos, Matrix.one_mul]
      funext k
      simp [Matrix.vecMul, dotProduct, x₀, B, Fin.sum_univ_succ, Matrix.one_apply, (Fin.succ_ne_zero k).symm]
    have hB : Bᴴ * Formalism.REAL.Jm (allPos (n + 1)) * B = Formalism.REAL.Jm (allPos n) := by
      rw [Jm_allPos, Jm_allPos, Matrix.mul_one]
      ext a b
      simp [Matrix.mul_apply, B, Matrix.one_apply, eq_comm]
    obtain ⟨j, -, hj⟩ := GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal (n + 1) n _ _ true x₀ B rfl
      hq hx hB
    have hV : ENNReal.ofReal c' * Formalism.REAL.muG (allPos n) Set.univ = ENNReal.ofReal (volU n) := by
      rw [← hv, ENNReal.ofReal_mul hc'pos.le, ENNReal.ofReal_toReal (muG_univ_lt_top n).ne]
    have key := GlobalTheory.T.gauge_measure_quotient_unitaryJ_vector_stabiliser n _ _ true x₀ B j hq hx hB hj c c' hc hc'
      (fun _ => ENNReal.ofReal (volU n)⁻¹) measurable_const (fun g => by
        rw [lintegral_const, mul_left_comm, hV, ← ENNReal.ofReal_mul (inv_pos.2 (volU_pos n)).le,
          inv_mul_cancel₀ (volU_pos n).ne', ENNReal.ofReal_one])
    have hs : sgn ℝ true = 1 := by simp [sgn]
    simp only [x₀, gauss_inv_single, lintegral_const] at key
    rw [hs, GlobalTheory.GaussMean.Sphere.gaussDens_sphere] at key
    have k2 := congrArg ENNReal.toReal key
    have hp := volU_pos n
    have hπ := Real.pi_pos
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcpos.le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofReal (inv_pos.2 hp).le,
      ENNReal.toReal_ofReal (by positivity)] at k2
    rw [volU_succ]
    have he := Real.exp_pos (-1)
    have hf : (0 : ℝ) < n.factorial := by positivity
    field_simp at k2 ⊢
    linarith

end GlobalTheory.UnitaryVolume
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.isContRep_kernel_integral_compact_support : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (C : Set B.I.GA), IsCompact C → (∀ᵐ z ∂((B.I.muA B.μf).restrict B.fund), z ∉ C → (y : B.I.GA → ℂ) z = 0) → IsContRep B (T y) (fun x => ∫ z in B.fund, kern B.I (phe B d) x z * (y : B.I.GA → ℂ) z ∂(B.I.muA B.μf)) := by
  first | exact @GlobalTheory.KernelContRep.isContRep_integral_kernel | exact GlobalTheory.KernelContRep.isContRep_integral_kernel | (intros; apply GlobalTheory.KernelContRep.isContRep_integral_kernel <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.diffQuotient_besselMap_tendsto : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (ψ : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (l : H → Wp) (x : H) (X : Mat k r), IsURepOn (GG k r) σ → IsBesselMapSm z ψ σ π l → IsSmoothVec σ x → InLieHpk k r X → Filter.Tendsto (fun t : ℝ => l ((t : ℂ)⁻¹ • (σ (NormedSpace.exp ((t : ℂ) • X)) x - x))) (nhdsWithin 0 {0}ᶜ) (nhds (l (dsig σ X x))) ∧ ContinuousOn (fun g => l (σ g x)) (GG k r) ∧ ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ GG k r ∧ σ (NormedSpace.exp ((t : ℂ) • X)) x - x = ∫ u in (0 : ℝ)..t, σ (NormedSpace.exp ((u : ℂ) • X)) (dsig σ X x) := by
  first | exact @GlobalTheory.diffQuot_bessel | exact GlobalTheory.diffQuot_bessel | (intros; apply GlobalTheory.diffQuot_bessel <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.exists_continuousRep_bounded_evaluation_rows : GlobalTheory.DSId.StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → 1 ≤ B.I.n → 1 ≤ B.g → ∃ C : ℝ, ∀ A ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ k ∈ B.I.Kg B.g, B.R (1, k) (A (B.tens B.w)) = A (B.tens B.w)) → ∃ f : B.I.GA → ℂ, IsContRep B (A (B.tens B.w)) f ∧ ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * ‖A (B.tens B.w)‖ := by
  first | exact @GlobalTheory.EvalBound.exists_contRep_bound | exact GlobalTheory.EvalBound.exists_contRep_bound | (intros; apply GlobalTheory.EvalBound.exists_contRep_bound <;> assumption)
end
