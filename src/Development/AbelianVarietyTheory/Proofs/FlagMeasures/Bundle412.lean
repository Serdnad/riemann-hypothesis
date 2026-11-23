module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle284
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle308
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle407
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle315
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle278
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle203
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle022
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPeriodPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle395
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocInOfUniqOfDecLow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle279
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle100
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle310
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle399
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle408
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.genericTerms_scalarClasses_form_family : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t = 1 ∧ (Y.tO u u').scal t' t) → (∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet, ∀ t'' ∈ (Y.tO u u').genSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t'' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t'' = 1 → (Y.tO u u').scal t' t'' → (Y.tO u u').s0 t t'' = 1 ∧ (Y.tO u u').scal t t'') → FamQ Y u u' Not (Y.tO u u').genSet (gCls Y u u') := by
  first | exact @GlobalTheory.SnFamGen.genFam | exact GlobalTheory.SnFamGen.genFam | (intros; apply GlobalTheory.SnFamGen.genFam <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.globalLattices_count_eq_prod_localCounts_badPlaces : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → ∀ y : Dat Z FP, (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) → {p | y p ≠ d0 p}.Finite → ((globSet G G' y).encard : ℝ≥0∞) = ∏ p ∈ P, ((locSet G G' p (y p)).encard : ℝ≥0∞) := by
  first | exact @GlobalTheory.GenMass.Fibre.fibre | exact GlobalTheory.GenMass.Fibre.fibre | (intros; apply GlobalTheory.GenMass.Fibre.fibre <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.SchurNorm

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (t : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (t • A) = ‖t‖ ^ 2 * hsNormSq A := by
  have h : hsInner (t • A) (t • A) = ((‖t‖ ^ 2 : ℝ) : ℂ) * hsInner A A := by
    simp only [hsInner, Finset.mul_sum, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hsNormSq, h, Complex.re_ofReal_mul, hsNormSq]

theorem ampJ_of_smul {k r : ℕ} {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ)
    (c : ℝ) (t t' : ℂ) {Φ Ψ : Mat k r → Wp} {Φ' Ψ' : Mat k r → Wq} (h : ∀ g ∈ GG k r, Φ g = t • Ψ g)
    (h' : ∀ g ∈ GG k r, Φ' g = t' • Ψ' g) {γ : Mat k r} (hγ : γ ∈ GG k r) :
    ampJ μ c Φ Φ' γ = ((c : ℂ)⁻¹ * (t * star t')) • ampJ μ 1 Ψ Ψ' γ := by
  unfold ampJ
  rw [Complex.ofReal_one, inv_one, one_smul, mul_smul, ← integral_smul (t * star t')]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [show ∀ᵐ x ∂μ, Matrix.of x ∈ GG k r from hμ.2.2.1] with x hx
  rw [h _ (Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hγ hx), h' _ hx]
  ext η
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.smul_apply,
    inner_smul_left, smul_smul, Complex.star_def]
  congr 1
  ring

theorem exists_isEll_smul (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp]
    (σ : Mat k r → (H →L[ℂ] H)) (v₀ : H) (a d c₀ : ℝ) (μG μS νS : Measure (Mt k r))
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (B : H → Wp) (hv : v₀ ≠ 0)
    (hS : StdSm σ (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀) a μG d) (hz : SideIrr z π μS) (hq : IsQuotMeas μG μS νS)
    (hm : MultOne z (psiGen k r z c) σ π) (hB : IsBesselMapSm z (psiGen k r z c) σ π B) (hc : 0 < c₀)
    (h0 : l2SG νS (fun g => B (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wp))
    (h1 : ∀ v ∈ smoothVecs σ, l2SG νS (fun g => B (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 =
      l2SG νS (fun g => B (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) :
    ∃ l : H → Wp, IsEll z (psiGen k r z c) π μS σ (DD σ (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀)) l ∧
      ∃ t : ℂ, ‖t‖ ^ 2 = c₀ * Module.finrank ℂ Wp * d ∧
        ∀ g ∈ GG k r, B (σ g v₀) = t • l (σ g (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀)) := by
  set w : H := ((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀ with hw
  have hn : ((‖v₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hv
  have hvw : v₀ = ((‖v₀‖ : ℝ) : ℂ) • w := by rw [hw, smul_smul, mul_inv_cancel₀ hn, one_smul]
  obtain ⟨hStd, hsm⟩ := hS
  have hU : IsURepOn (GG k r) σ := hStd.2.1
  have hw1 : ‖w‖ = 1 := hStd.2.2.2.1
  have hw1' : ‖w‖₊ = 1 := NNReal.eq hw1
  have hG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hd : 0 < d := hStd.2.2.2.2.2.1.1
  obtain ⟨-, -, hle, hact, hinf⟩ := GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hU
  have hgw : ∀ g ∈ GG k r, σ g w ∈ smoothVecs (k := k) (r := r) σ := (hact w hsm).1
  haveI : Nontrivial Wp := hz.2.2
  have hdim : (0 : ℝ) < Module.finrank ℂ Wp := by exact_mod_cast Module.finrank_pos
  have hn0 : ((‖v₀‖₊ : ℝ≥0∞)) ^ 2 ≠ 0 := pow_ne_zero _ (by simpa using hv)
  have hnt : ((‖v₀‖₊ : ℝ≥0∞)) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hLw : l2SG νS (fun g => B (σ g w)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS (fun g => B (σ g v₀)) := by
    rw [h1 w hsm, hw1']; simp
  have hnv : NonVan z (psiGen k r z c) σ π w μG νS := by
    refine GlobalTheory.T.exists_nonzero_fixed_of_squareIntegrable_bessel k r σ w a d μG μS νS z c π B ⟨hStd, hsm⟩ hz.1 hq hB ?_ ?_ ?_
    · intro h
      rw [h, zero_mul, h0] at hLw
      exact (ENNReal.ofReal_pos.2 (mul_pos hc hdim)).ne hLw
    · intro h
      rw [h, ENNReal.top_mul hn0, h0] at hLw
      exact ENNReal.ofReal_ne_top hLw.symm
    · intro v hv'
      refine (ENNReal.mul_left_inj hn0 hnt).1 ?_
      rw [h1 v hv', ← hLw]; ring
  obtain ⟨l, hl⟩ := GlobalTheory.T.exists_besselMap_rankOne_factorisation_translateSpan k r σ w a μG d z c π μS hStd hz.1 hsm hm νS hq hnv
  refine ⟨l, hl, ?_⟩
  have hs : ∃ s : ℂ, ∀ x ∈ smoothVecs (k := k) (r := r) σ, B x = s • l x := by
    obtain ⟨s, hs | hs⟩ := hm B l hB hl.1
    · exact ⟨s, hs⟩
    · obtain ⟨u, hu, hu0⟩ := hl.2.1
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hu0 ((hs u ((hinf hsm).1 u (hle hu))).trans (zero_smul _ _))
      exact ⟨s⁻¹, fun x hx => by rw [hs x hx, smul_smul, inv_mul_cancel₀ hs0, one_smul]⟩
  obtain ⟨s, hs⟩ := hs
  have key : ∀ g ∈ GG k r, B (σ g v₀) = (((‖v₀‖ : ℝ) : ℂ) * s) • l (σ g w) := by
    intro g hg
    have e : σ g v₀ = ((‖v₀‖ : ℝ) : ℂ) • σ g w := by rw [← map_smul, ← hvw]
    rw [e, hB.2.1 _ _ (hgw g hg), hs _ (hgw g hg), smul_smul]
  refine ⟨_, ?_, key⟩
  generalize ((‖v₀‖ : ℝ) : ℂ) * s = t at key
  have hone : (1 : Mat k r) ∈ GG k r := by simp [UH]
  have hwD : w ∈ DD σ w := by
    have := mem_DD σ w hone
    rwa [hU.1.1] at this
  have hlw := (GlobalTheory.T.besselModel_projector_on_line k r σ w a μG d z c π μS hStd hz.1 νS hq l hl).1 w hwD
  have hμS : IsHaarOn (Sset k r z) μS := hz.1.2.2.2.1
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hμS.2.1 (measure_mono_null (by
    rintro x hx ⟨h, hh, m, hm', e⟩
    exact hx (e ▸ Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hh.1 hm'.1)) hμS.2.2.1) hq
  have e : l2SG νS (fun g => B (σ g v₀)) = ENNReal.ofReal (‖t‖ ^ 2) * l2SG νS (fun x => l (σ x w)) := by
    unfold l2SG
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [key _ hx, nnnorm_smul, ENNReal.coe_mul, mul_pow, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  rw [h0, hlw, hw1, ← ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at e
  rw [e]; field_simp

theorem lintegral_hsNormSq_ampJ_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (v₀ : H) (a d c₀ : ℝ) (μG μS μS' νS νS' ν : Measure (Mt k r)) (z z' : (Fin (2 * r + k + 1) → ℂ)) (c c' : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (B : H → Wp) (B' : H → Wq), v₀ ≠ 0 → StdSm σ (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀) a μG d → SideIrr z π μS → SideIrr z' π' μS' → IsQuotMeas μG μS νS → IsQuotMeas μG μS' νS' → MultOne z (psiGen k r z c) σ π → MultOne z' (psiGen k r z' c') σ π' → IsBesselMapSm z (psiGen k r z c) σ π B → IsBesselMapSm z' (psiGen k r z' c') σ π' B' → 0 < c₀ → l2SG νS (fun g => B (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wp) → l2SG νS' (fun g => B' (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wq) → (∀ v ∈ smoothVecs σ, l2SG νS (fun g => B (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS (fun g => B (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) → (∀ v ∈ smoothVecs σ, l2SG νS' (fun g => B' (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS' (fun g => B' (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) → IsDis (Greg k r z z') μG μS μS' ν → ∫⁻ γ, ENNReal.ofReal (hsNormSq (ampJ μG c₀ (fun g => B (σ g v₀)) (fun g => B' (σ g v₀)) (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal ((Module.finrank ℂ Wp : ℝ) * Module.finrank ℂ Wq / d) := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ v₀ a d c₀ μG μS μS' νS νS' ν z z' c c' π π' B B' hv hS hz hz' hq hq'
    hm hm' hB hB' hc h0 h0' h1 h1' hν
  obtain ⟨l, hl, t, ht, key⟩ := exists_isEll_smul k r σ v₀ a d c₀ μG μS νS z c π B hv hS hz hq hm hB hc h0 h1
  obtain ⟨l', hl', t', ht', key'⟩ :=
    exists_isEll_smul k r σ v₀ a d c₀ μG μS' νS' z' c' π' B' hv hS hz' hq' hm' hB' hc h0' h1'
  set w : H := ((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀ with hw
  have hG : IsHaarOn (GG k r) μG := hS.1.2.2.2.2.1
  have hd : 0 < d := hS.1.2.2.2.2.2.1.1
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have h5 := GlobalTheory.T.lintegral_hsNormSq_matrixCoeff_le_formalDegree k r σ w a μG d z c π μS z' c' π' μS' hS.1 hz.1 hz'.1 ν hν l l' hl hl'
  have hJ := (GlobalTheory.T.amplitude_eq_ampJ_and_bessel_eq_doubleIntegral k r (H := H) (Wp := Wp) (Wq := Wq)).1 μG (fun x => l (σ x w)) (fun x => l' (σ x w)) hG
  have hD : (0 : ℝ) ≤ (Module.finrank ℂ Wp : ℝ) * Module.finrank ℂ Wq := by positivity
  rw [div_eq_mul_inv, ENNReal.ofReal_mul hD]
  refine le_trans (le_of_eq ?_) (mul_le_mul_right h5 _)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [show ∀ᵐ γ ∂ν, Matrix.of γ ∈ Greg k r z z' from hν.2.1] with γ hγ
  rw [ampJ_of_smul hG c₀ t t' (Ψ := fun x => l (σ x w)) (Ψ' := fun x => l' (σ x w)) key key' hγ.1,
    ← hJ _ hγ.1, ← ENNReal.ofReal_mul hD, hsNormSq_smul, hsNormSq_smul]
  congr 1
  rw [norm_mul, norm_mul, norm_star, norm_inv, mul_pow, mul_pow, ht, ht', Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hc.le, Real.norm_of_nonneg hd.le]
  field_simp

end GlobalTheory.Amp.SchurNorm
end

section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowMainEqP_of_cut (hCh : PN.NGChain) (hMG : MeanAmpGen) (hc : GenCutP) : RowMainEqP := by
  intro Cg cb Cw cT CT C0 A hcb hcT
  obtain ⟨C1, C0n, Aexp, CB, CSt, Cgs, CTs, h1, h2, h3, h4, hA, C'₀, Cl₀, h⟩ := hc Cg cb Cw cT CT C0 A hcb hcT
  obtain ⟨Cn, hCn, hK⟩ := rowGenJoint_of hCh hMG C1 C0n Aexp CB CSt Cgs CTs h1 h2 h3 h4 hA
  refine ⟨Cn, hCn, C'₀, Cl₀, fun C' Cl a b D large₂ X Y u hTies hH hT ha => ?_⟩
  obtain ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, _, _, hG, hdd, hN, hF, hS, hIn⟩ :=
    h C' Cl a b D large₂ X Y u hTies hH hT
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u) _ _ _ _ (Y.tO u u) D.R.rS D.R.k (Set (TauC Y u u)) (NuC D)
    (NOfG Y u νL νB ng) P B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
    cSt e1 Irat Ire
  rw [hcard] at key
  have r := key ha hG hN hF hS hIn
  rw [hdd] at r
  exact r

end GlobalTheory.SnPos
end
end

section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

noncomputable section

open scoped Classical

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepAnalyticCGP_of_steps : StepPinExists → StepTermVanishG → StepLocGenPinnedG → StepThmBGP →
    StepAnalyticCGP := by
  intro hE hV hL hB Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, CSt, hCSt, a₀, b₀, hL2⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨e₀, f₀, hE2⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨v₀, w₀, hV2⟩ := hV Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, hCB, p₀, q₀, hB2⟩ := hB Cg cb Cw cT CT C0 hcb hcT A
  refine ⟨CB, CSt, hCB, hCSt, max a₀ (max e₀ (max v₀ p₀)), max b₀ (max f₀ (max w₀ q₀)),
    fun C' Cl h1 h2 D large₂ X Y u hTi hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk => ?_⟩
  have ha1 : a₀ ≤ C' := le_trans (by simp) h1
  have ha2 : b₀ ≤ Cl := le_trans (by simp) h2
  have he1 : e₀ ≤ C' := le_trans (by simp) h1
  have he2 : f₀ ≤ Cl := le_trans (by simp) h2
  have hv1 : v₀ ≤ C' := le_trans (by simp) h1
  have hv2 : w₀ ≤ Cl := le_trans (by simp) h2
  have hp1 : p₀ ≤ C' := le_trans (by simp) h1
  have hp2 : q₀ ≤ Cl := le_trans (by simp) h2
  obtain ⟨ν, hν⟩ := hE2 C' Cl he1 he2 D large₂ X Y u u hc
  obtain ⟨s, ng, e1, hs1, hs0, hsb, he0, he3, hLoc, hGen⟩ :=
    hL2 C' Cl ha1 ha2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν
  have hb0 : 0 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) :=
    le_trans (sq_nonneg _) (hsb 1)
  exact ⟨sc s ν, ν, ng, large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f), e1,
    Formalism.L2.SG.NGAnalytic.nuQOK_sc u u s hs1 hs0 ν hν.1, hν.1, hb0, le_rfl, he0, he3,
    ampVanishG_sc Y u s hs0 ν (ampVanishG_of_term Y u ν (hV2 C' Cl hv1 hv2 D large₂ X Y u hc ν hν)), hLoc, hGen,
    measureInputG_sc Y u s ν _ hsb ng,
    hB2 C' Cl hp1 hp2 D large₂ X Y u hTi hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν (sc s ν) ng⟩

end GlobalTheory.SnPos
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepAnalyticGP_of (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hA : StepAnalyticCGP) : StepAnalyticGP := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨k₀, l₀, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨m₀, n₀, hT2⟩ := hTi Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, CSt, h1, h2, a₀, b₀, hA2⟩ := hA1 A
  refine ⟨CB, CSt, h1, h2, max a₀ (max k₀ m₀), max b₀ (max l₀ n₀), fun C' Cl e1 e2 D large₂ X Y u hD hc => ?_⟩
  obtain ⟨hb, X0, ψ, hT⟩ := hT2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc hb X0 ψ hT
  have hBk' := massDataValid_unscale (kapU_pos D) hBk
  obtain ⟨νL, νB, ng, cSt, e, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
    hA2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u hD hc hb X0 ψ hT sd C Th
      F0 what₂ vR Q i0 i0' νq (Irat * kapU D) (Ire * kapU D) hBk'
  exact ⟨_, inferInstance, _, Irat * kapU D, Ire * kapU D, νL, νB, ng, cSt, e, hBk', a1, a2, a3, a4, a5, a6, a7,
    a8, a9, a10, a11⟩

end GlobalTheory.SnPos
end
end

section

noncomputable section

open scoped Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem genCutP_of_steps (hS : StepSizes) (hC : StepClassG) (hN : StepNormalsG) (hP : StepPointsG)
    (hH : StepHeightG) (hA : StepAnalyticGP) : GenCutP := by
  intro Cg cb Cw cT CT C0 A0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CB, CSt, hCB, hCSt, a₀, b₀, hA2⟩ := hA1 (C1 + C0n + 38)
  obtain ⟨Cgs, CTs, hCg, hCT, s₀, t₀, hS2⟩ := hS Cg cb Cw cT CT C0
  obtain ⟨n₀, m₀, hN2⟩ := hN Cg cb Cw cT CT C0
  obtain ⟨p₀, q₀, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨h₀, j₀, hH2⟩ := hH Cg cb Cw cT CT C0
  refine ⟨C1, C0n, C1 + C0n + 38, CB, CSt, Cgs, CTs, hCB, hCSt, hCg, hCT, le_refl _,
    max a₀ (max s₀ (max n₀ (max p₀ h₀))), max b₀ (max t₀ (max m₀ (max q₀ j₀))),
    fun C' Cl h1 h2 D large₂ X Y u hTies hHy hT => ?_⟩
  have hc : Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u := ⟨hHy.1, hHy.2.1, hT⟩
  have e1' : a₀ ≤ C' := le_trans (le_max_left _ _) h1
  have e2' : b₀ ≤ Cl := le_trans (le_max_left _ _) h2
  have f1 : s₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h1
  have f2 : t₀ ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h2
  have i1 : n₀ ≤ C' :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) h1
  have i2 : m₀ ≤ Cl :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) h2
  have j1 : p₀ ≤ C' := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h1
  have j2 : q₀ ≤ Cl := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h2
  have k1 : h₀ ≤ C' := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h1
  have k2 : j₀ ≤ Cl := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h2
  obtain ⟨P, iP, B, Irat, Ire, νL, νB, ng, cSt, e1, hBk, hL, hBq, c1, c2, c3, c4, hV, hLoc, hGen, hMeas, hSum⟩ :=
    hA2 C' Cl e1' e2' D large₂ X Y u hTies hc
  obtain ⟨hG, hdd, hNI, hFI⟩ := hBk
  refine ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, hL, hBq, hG, hdd, hNI, hFI,
    Formalism.L2.SG.NGCut.ngSizes_of (hS2 C' Cl f1 f2 D large₂ X Y u u hc) c1 c2 c3 c4, ?_⟩
  exact ⟨classInputG_of Y u (hC D X Y u (g_ge_three hc) hT) νL νB ng, ampInputG_of_vanish Y u νL νB ng hV,
    hN2 C' Cl i1 i2 D large₂ X Y u hc νL νB ng, hP2 C' Cl j1 j2 D large₂ X Y u hc νL νB ng, hLoc, hMeas, hGen,
    hH2 C' Cl k1 k2 D large₂ X Y u hc νL νB ng, hSum⟩

end GlobalTheory.SnPos
end
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
noncomputable section

namespace GlobalTheory.AmpTKGap

variable {k r : ℕ}

theorem side_bessel (hH : GlobalTheory.GapIn.Hyp) (L : LocBessel k r) (h : ℝ) (hgap : GapAtLeast L.ε L.lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hc : L.c ≠ 0) (hκ0 : 0 < L.κN) (hκt : L.κN ≠ ⊤)
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (u : Fin k → ℝ) (μW : Measure (Mt k r)) (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : IsHCTypeW k r z u π)
    (hW : IsHaarOn (UWset k r z) μW) :
    ∃ l : L.Hs → Wp, (∀ x ∈ (GlobalTheory.AmpTK.rep L).sm, ∀ v ∈ (GlobalTheory.AmpTK.rep L).TK,
      Formalism.FourierDecayAlt.ThreeDimData.be z L.c π L.σ μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) ∧ GlobalTheory.AmpTK.SmCW L l := by
  haveI := FiniteDimensional.complete ℂ Wp
  obtain ⟨μG, hG⟩ := GlobalTheory.SnMass.Inhab.exists_isHaarOn k r
  have hN := GlobalTheory.haarLie_isHaarOn_Nset k r L.κN hκ0 hκt.lt_top
  obtain ⟨νq, hq⟩ := GlobalTheory.exists_isQuotMeas_bessel_subgroup k r z μW L.μN μG hz hT hW hN hG
  obtain ⟨U, hS⟩ := GlobalTheory.AmpNormal.sideG_of hκt.lt_top hz hT hπ hW hG hq
  obtain ⟨t, ht, htN, htz, -⟩ := GlobalTheory.TorusScale.exists_torus_scale k r L.c hc
  obtain ⟨-, htc, hψ⟩ := htz z hz
  have hR : Formalism.MainNotions.S.IsURepOn (GG k r) (GlobalTheory.AmpTK.rep L).σ := GlobalTheory.Amp.LocalInputs.urep_of_ds L.hσ
  obtain ⟨hS', hB⟩ := GlobalTheory.T.isBesselMap_conj_iff_and_besselFn_eq_rankOne hH k r Wp z π U L.c μW L.μN μG νq t ht htN htc hψ hS
  obtain ⟨-, hbe⟩ := hB (GlobalTheory.AmpTK.rep L) hR
  have hDG : (GlobalTheory.AmpTK.rep L).IsDG L.ε L.lam := ⟨L.hlam, L.hσ, h, hgap, hok⟩
  obtain ⟨l₁, hl₁⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r L.ε L.lam h (GlobalTheory.AmpTK.rep L) Wp z π U μW _ μG _ hDG hgap hok hS'
  have hti := GlobalTheory.BesselMove.inv_mem ht
  refine ⟨fun v => l₁ ((GlobalTheory.AmpTK.rep L).σ t⁻¹ v), fun x hx v hv => hbe l₁ hl₁ x hx v hv, ?_, ?_, ?_⟩
  · intro v hv w hw
    show l₁ ((GlobalTheory.AmpTK.rep L).σ t⁻¹ (v + w)) = _
    rw [map_add (f := _)]
    exact hl₁.1.1 _ (GlobalTheory.BesselMove.sig_sm hR hti hv) _ (GlobalTheory.BesselMove.sig_sm hR hti hw)
  · intro a v hv
    show l₁ ((GlobalTheory.AmpTK.rep L).σ t⁻¹ (a • v)) = _
    rw [map_smul]
    exact hl₁.1.2.1 _ _ (GlobalTheory.BesselMove.sig_sm hR hti hv)
  · exact GlobalTheory.SmMapAct.cw_comp (GlobalTheory.BesselMove.smMap_sigma hR hti) hl₁.1.2.2.2

theorem exists_besselTK : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ),
    Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.c ≠ 0 → 0 < L.κN → L.κN ≠ ⊤ →
    ∃ (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq), GlobalTheory.AmpTK.BeTK L l l' ∧ GlobalTheory.AmpTK.SmCW L l ∧ GlobalTheory.AmpTK.SmCW L l' := by
  intro hH k r L h hgap hok hc hκ0 hκt
  obtain ⟨l, hl, hsl⟩ := side_bessel hH L h hgap hok hc hκ0 hκt L.z L.π L.u L.μW L.hz.1 L.hz.2 L.hπ L.hμW.1
  obtain ⟨l', hl', hsl'⟩ := side_bessel hH L h hgap hok hc hκ0 hκt L.z' L.π' L.u' L.μW' L.hz'.1 L.hz'.2 L.hπ' L.hμW'.1
  exact ⟨l, l', ⟨hl, hl'⟩, hsl, hsl'⟩

end GlobalTheory.AmpTKGap
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

theorem _root_.GlobalTheory.T.rationalRootCoordinates_eq_frameMatrix : ∀ (D : D7) (X : HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ s y : X.B.I.Ginf) (τ : D.what₂.Tau) (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), GlobalTheory.LoopAct.IsMatOn (uMat ((γ⁻¹ * (s⁻¹ * y * s) * γ) (X.pl.symm τ))) (Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ)) M → ∀ q : GlobalTheory.LoopV.roots (ptMat w), GlobalTheory.LoopVol.ratCoord X u' w γ s y τ q = M q.1.1 q.1.2 := by
  first | exact @GlobalTheory.LoopVol.ratCoord_eq_matOn | exact GlobalTheory.LoopVol.ratCoord_eq_matOn | (intros; apply GlobalTheory.LoopVol.ratCoord_eq_matOn <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

theorem _root_.GlobalTheory.T.frameGram_mul_eq_conjTranspose_mul_frameMatrices : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (g γ h : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (C B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), GlobalTheory.LoopAct.IsMatOn (uMat (g⁻¹ v)) (Formalism.L2.SG.RealObj.frm X u 1 v) C → GlobalTheory.LoopAct.IsMatOn (uMat (h v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) B → Formalism.L2.SG.RealObj.ZX X u u' 1 (g * γ * h) v = Cᴴ * Formalism.L2.SG.RealObj.ZX X u u' 1 γ v * B := by
  first | exact @GlobalTheory.ZxMul.zx_mul | exact GlobalTheory.ZxMul.zx_mul | (intros; apply GlobalTheory.ZxMul.zx_mul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

theorem _root_.GlobalTheory.T.frameMatrix_mem_unipotentStabilizer_frameGram : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ y : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), y ∈ Formalism.L2.SG.RealObj.StInf X u u' γ → IsUpUni M → GlobalTheory.LoopAct.IsMatOn (uMat ((γ⁻¹ * y * γ) v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) M → IsUnit (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v).det → M ∈ GlobalTheory.LoopV.stabU (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v) := by
  first | exact @GlobalTheory.FrameStab.frameMat_mem_stabU | exact GlobalTheory.FrameStab.frameMat_mem_stabU | (intros; apply GlobalTheory.FrameStab.frameMat_mem_stabU <;> assumption)
end
