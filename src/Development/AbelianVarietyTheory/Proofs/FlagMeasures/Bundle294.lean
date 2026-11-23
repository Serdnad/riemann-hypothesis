module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle174
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle210
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle155
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle229
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralLeOfHighest
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle258
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle048
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle065
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle060
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle028
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle085
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle087
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusWeightEigenAndRootShift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle034
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVecUnitaryModule
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.CoreDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle004
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.VectorComplexifiedDerivativeCommutator
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassClassEqWeightCount
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle013
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.CentreLow

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem smooth_comb {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') : SmoothOnG ε (fun h => f h + c * f' h) := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', e'⟩ := hf' g hg
  refine ⟨U ∩ U', fun h => F h + c * F' h, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (contDiffOn_const.mul (hF'.mono Set.inter_subset_right)), ?_⟩
  intro x hx hxJ
  simp only [e x hx.1 hxJ, e' x hx.2 hxJ]

theorem smooth_word {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    (w : List (Fin n × Fin n)) : SmoothOnG ε (Eword ε w f) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    have hc := complex_parts_mem_lie_algebra_holds n ε (Matrix.single p.1 p.2 1)
    exact smooth_comb Complex.I (rdSmooth_of right_derivative_extends n ε _ _ ih hc.1)
      (rdSmooth_of right_derivative_extends n ε _ _ ih hc.2.1)

theorem word_comb {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') (w : List (Fin n × Fin n)) :
    ∀ g, inUJ ε g → Eword ε w (fun h => f h + c * f' h) g = Eword ε w f g + c * Eword ε w f' g := by
  induction w with
  | nil => intro g _; rfl
  | cons p w ih =>
    intro g hg
    have hc := complex_parts_mem_lie_algebra_holds n ε (Matrix.single p.1 p.2 1)
    have h1 := Eword_congr ε ih [p] g hg
    have h2 := fun X hX => (right_derivative_linear n ε _ _ X X 0 c g (smooth_word hf w) (smooth_word hf' w) hX hX hg).2.2
    refine Eq.trans h1 ?_
    simp only [Eword, Eab, Ec, id, h2 _ hc.1, h2 _ hc.2.1]
    ring

theorem gelf_comb {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    gelf ε m (fun h => f h + c * f' h) g = gelf ε m f g + c * gelf ε m f' g := by
  simp only [gelf, word_comb c hf hf' _ g hg, Finset.sum_add_distrib, Finset.mul_sum]

theorem gelf_congr {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g, inUJ ε g → f g = f' g) (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    gelf ε m f g = gelf ε m f' g :=
  Finset.sum_congr rfl fun _ _ => Eword_congr ε h _ g hg

theorem centre_scalar_low : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∃ c : ℕ → ℂ, ∀ s ∈ lowKSub ε lam σ, ∀ u : H, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ) ∧ ∀ m, ∀ g ∈ UJset ε, gelf ε m (fun x => ⟪u, σ x s⟫_ℂ) g = c m * ⟪u, σ g s⟫_ℂ := by
  intro n ε lam H _ _ _ σ hσ hK
  obtain ⟨α, hα, hαc, hfix⟩ := GlobalTheory.T.exists_smooth_compactSupport_fix_lowestKType n ε lam H σ hσ hK
  have hD := fun (s : lowKSub ε lam σ) => GlobalTheory.T.derivatives_coefficients_convolutionFixed_vector n ε H σ α s hσ hα hαc (hfix s s.2)
  have hsm : ∀ (s : lowKSub ε lam σ) (u : H), SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ) := fun s => (hD s).1
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by simp [UJset, inUJ]
  have hone : ∀ v, σ 1 v = v := fun v => by rw [hσ.1.1]; rfl
  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, ∀ v, σ (a * b) v = σ a (σ b v) := fun a ha b hb v => by
    rw [hσ.1.2 a ha b hb]; rfl
  have hC : ∀ (m : ℕ) (s : lowKSub ε lam σ), ∃ s' : H, ∀ u, ∀ g ∈ UJset ε,
      gelf ε m (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g s'⟫_ℂ := by
    intro m s
    choose v hv using (hD s).2
    refine ⟨∑ a : Fin (m + 1) → Fin n, v (cycWord a), fun u g hg => ?_⟩

    simp only [gelf, hv _ u g hg, map_sum, inner_sum]
  choose C hC using hC
  have hC1 : ∀ (m : ℕ) (s : lowKSub ε lam σ) (u : H),
      ⟪u, C m s⟫_ℂ = gelf ε m (fun x => ⟪u, σ x s⟫_ℂ) 1 := fun m s u => by rw [hC m s u 1 h1, hone]
  have hlin : ∀ (m : ℕ) (c : ℂ) (s t : lowKSub ε lam σ), C m (s + c • t) = C m s + c • C m t := by
    intro m c s t
    refine ext_inner_left ℂ fun u => ?_
    rw [inner_add_right, inner_smul_right, hC1, hC1, hC1, ← gelf_comb c (hsm s u) (hsm t u) m 1 h1]
    simp [inner_add_right, inner_smul_right]
  have h0 : ∀ m, C m 0 = 0 := fun m => by simpa using hlin m 1 0 0
  have key : ∀ m, ∃ c : ℂ, ∀ s : lowKSub ε lam σ, C m s = c • (s : H) := by
    intro m
    refine GlobalTheory.T.kMap_lowestKTypeSubspace_eq_scalar n ε lam H σ hσ hK
      { toFun := C m
        map_add' := fun s t => by simpa using hlin m 1 s t
        map_smul' := fun c t => by simpa [h0] using hlin m c 0 t } ?_
    intro k hk s s' e
    have hkU : k ∈ UJset ε := (maximal_compact_facts n ε).1 k hk
    refine ext_inner_left ℂ fun u => ?_
    change ⟪u, C m s'⟫_ℂ = ⟪u, σ k (C m s)⟫_ℂ
    rw [hC1, ← hC m s u k hkU, ← Matrix.one_mul k,
      ← GlobalTheory.T.gelfandInvariant_comm_rightTranslation n ε m _ k 1 (hsm s u) hkU h1]
    refine gelf_congr (fun g hg => ?_) m 1 h1
    rw [e, hmul g hg k hkU]
  choose c hc using key
  refine ⟨c, fun s hs u => ⟨hsm ⟨s, hs⟩ u, fun m g hg => ?_⟩⟩
  rw [hC m ⟨s, hs⟩ u g hg, hc, map_smul, inner_smul_right]

end GlobalTheory.CentreLow
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowTypeMassGap

section prelim

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset GlobalTheory.LowTypeMass
open scoped InnerProductSpace ENNReal

variable {k r : ℕ}

theorem lev_zero_of_wt_gap (hH : HypsG) (hk : 1 ≤ k) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {R : Rep k r} (hR : R.IsDG ε mu) {Q : Mx k r}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub} (hQ : PI.UpqRep.IsCayleyU k r ε Q)
    (hE : R.IsE Q E) (S : Submodule ℂ R.H) (hfin : FiniteDimensional ℂ S)
    (hst : PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S)
    (hmax : ∀ (μ : Fin (2 * r + k + 1) → ℝ) (v : R.H), v ∈ S → v ≠ 0 →
      PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) μ v →
      PI.UpqRep.CDom ε μ (Formalism.QuantumDeterminants.lowK ε mu))
    (w : R.smSub) (hwS : (w : R.H) ∈ S)
    (hw : PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) (Formalism.QuantumDeterminants.lowK ε mu) (w : R.H)) :
    Lev ε E mu 0 w := by
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hRS : R.IsDS ε mu := GlobalTheory.isDS_of_isDG hR
  obtain ⟨-, hS2⟩ := GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r ε mu R hRS Q hQ S hfin hst
  obtain ⟨hw1, hw2⟩ := GlobalTheory.TorusWeight.torus_weight_action hK k r ε mu R hRS Q E hQ hE (Formalism.QuantumDeterminants.lowK ε mu) w hw
  have hMod := Gp91.GlobalTheory.isMod_smooth_of_isDS hH k r ε mu R hk hR Q E hQ hE
  refine GlobalTheory.lev_zero_of_kHighest _ _ _ E _ w hMod.1 hMod.2.1 ⟨hw1, ?_⟩ ?_
  · intro a b hab he
    by_contra h0
    have hmem : ((E a b w : R.smSub) : R.H) ∈ S := by
      rw [hE a b w]; exact hS2 a b he _ hwS
    have h0' : ((E a b w : R.smSub) : R.H) ≠ 0 := fun h => h0 (Subtype.ext h)
    exact GlobalTheory.DominantRootSums.not_cDom_add_root _ ε _ a b hab (hmax _ _ hmem h0' (hw2 a b))
  · have hle : Formalism.REAL.kSpan ε E w ≤ S.comap R.smSub.subtype := by
      refine sInf_le ⟨hwS, ?_⟩
      intro a b he x hx
      show ((E a b x : R.smSub) : R.H) ∈ S
      rw [hE a b x]; exact hS2 a b he _ hx
    have : FiniteDimensional ℂ (S.comap R.smSub.subtype) :=
      FiniteDimensional.of_injective
        ((R.smSub.subtype.comp (S.comap R.smSub.subtype).subtype).codRestrict S (fun x => x.2))
        (fun x y h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h'))
    exact Submodule.finiteDimensional_of_le hle

theorem weightedMass_bound_lowestType_largeGap (hH : GlobalTheory.GapIn.Hyp) (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r))
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ)
    (hS : Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg) (ν : Fin (2 * r + k + 1) → ℤ) (hν0 : n1 ν ≤ q0)
    (φ : (Fin (r + 1) → ℝ) → ℝ) (Bd : ℝ≥0∞) (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hbd : ∀ (Q : Mx k r) (E : ∀ ν', Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub),
      PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q →
      (∀ ν', n1 ν' ≤ q0 → (R ν').IsE Q (E ν') ∧ Formalism.REAL.GlRel (E ν')) →
      ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w → ‖w‖ = 1 →
      ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) *
        (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd)
    (w : (R ν).H)
    (hw : PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w) :
    ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) *
      (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd := by
  classical
  have hK : PI.KFinSmooth := hH.1.1.2.2.1
  have hNum := hS.1
  have hFam := hS.2.1
  have hSide := hS.2.2.1
  have hSF := hS.2.2.2
  have hk : 1 ≤ k := hNum.1
  obtain ⟨Q, hQ, hw1, hwL⟩ := hw
  have hQu : IsUnit Q := hQ.1.1
  have hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E, hE⟩ := GlobalTheory.smooth_gl_module hK k r _ _ (R ν') (hFam ν' h') Q hQu
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hE
  have hbd' := hbd Q E hQ hE
  have hDG : (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) :=
    GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.1 k r lam u b bv ga h q0 R hNum hFam ν hν0
  have hDS := GlobalTheory.isDS_of_isDG hDG
  have hD := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 _ _ _ hDS Q hQ
  obtain ⟨hG, -, hlen, hmeas⟩ := GlobalTheory.quotMeas_ae_mem_and_measurable hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide
  obtain ⟨hBeL, hdg, -⟩ := hSF ν hν0
  obtain ⟨hmul, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r _ _ (R ν) hDS
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hSide.2.1
  have hsmS : ∀ S : Submodule ℂ (R ν).H, FiniteDimensional ℂ S →
      PI.UpqRep.IsKStableOn (PI.BesselPeriodGGP.eps48 k r) (fun g => (R ν).σ (Q⁻¹ * g * Q)) S → S ≤ (R ν).smSub :=
    fun S h1 h2 v hv => ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r _ _ (R ν) hDS Q hQ S h1 h2).1 v hv).2
  have hlenv : AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a) νq :=
    aemeasurable_pi_iff.2 hlen
  rcases eq_or_ne Bd ⊤ with rfl | hBd
  · exact le_top
  have hCB : ENNReal.ofReal Bd.toReal = Bd := ENNReal.ofReal_toReal hBd
  rw [← hCB]
  rw [← hCB] at hbd'
  have key := GlobalTheory.MomOne.lintegral_le_of_highest (m := νq) hD.2.2.1 _ (R ν).smSub hsmS
    (fun v x => ((Real.sqrt (φ (fun a => lenA k r z (Matrix.of x) a)) * Real.sqrt (dg ν) : ℝ) : ℂ) •
      lb ν ((R ν).σ (Matrix.of x) v))
    ?_ ?_ ?_ ?_ Bd.toReal ENNReal.toReal_nonneg ?_ w hwL hw1
  · simpa only [norm_sq_sqrt_scaled (hφ0 _) hdg.le] using key
  · intro v hv v' hv'
    filter_upwards [hG] with x hx
    simp only [Pi.add_apply]
    rw [map_add (f := _), hBeL.1.1 _ (hsm _ hx v hv) _ (hsm _ hx v' hv'), smul_add]
  · intro c v hv
    filter_upwards [hG] with x hx
    simp only [Pi.smul_apply]
    rw [map_smul, hBeL.1.2.1 c _ (hsm _ hx v hv), smul_comm]
  · intro v hv
    refine (Complex.continuous_ofReal.comp_aestronglyMeasurable ?_).smul (hmeas (lb ν) hBeL.1 v hv)
    exact (((hφm.comp_aemeasurable hlenv).sqrt).mul_const _).aestronglyMeasurable
  · intro g hg v hv
    obtain ⟨hgG, hgU⟩ := GlobalTheory.MomOne.conj_back hQ hg
    simp only [norm_sq_sqrt_scaled (hφ0 _) hdg.le]
    have hBc := (GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r _ _ (R ν) hDS Wp (lb ν) hBeL.1.1 hBeL.1.2.1
      hBeL.1.2.2.2 v hv).1
    have hF := measurable_piecewise_mass z hSide.1 hT φ hφm (dg ν) (fun x => lb ν ((R ν).σ x v)) hBc
    have := lintegral_rmul_of_measurable hSide
      (fun x => ENNReal.ofReal (φ (fun a => lenA k r z x a)) * ENNReal.ofReal (dg ν * ‖lb ν ((R ν).σ x v)‖ ^ 2))
      hF ?_ hgG
    · have e1 : ∀ x : Formalism.QuantumDeterminants.Mt k r, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) *
          (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2)) =
          ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a)) *
            ENNReal.ofReal (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) :=
        fun x => ENNReal.ofReal_mul (hφ0 _)
      simp only [e1]
      rw [← this]
      refine lintegral_congr_ae ?_
      filter_upwards [hG] with x hx
      simp only [GlobalTheory.MomOne.lenA_mul_unitary z _ hgU, hmul _ hx _ hgG]
      rw [ENNReal.ofReal_mul (hφ0 _)]
    · intro s hs x hx
      have e := (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.2 s hs
      obtain ⟨h', hh, m, hmN, rfl⟩ := hs
      obtain ⟨u₀, hπ⟩ := hSide.2.2.1
      have hsG : h' * m ∈ GG k r := Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hh.1 hmN.1
      beta_reduce
      simp only [e]
      rw [hmul _ hsG _ hx, hBeL.1.2.2.1 h' hh m hmN _ (hsm _ hx v hv), norm_smul,
        Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_norm, one_mul, Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hπ h' hh]
  · intro S hfd hst hcd v hv hv1 hwt
    simp only [norm_sq_sqrt_scaled (hφ0 _) hdg.le]
    have hvs : v ∈ (R ν).sm := hsmS S hfd hst hv
    have hLev := lev_zero_of_wt_gap hH.1 hk hDG hQ (hE ν hν0).1 S hfd hst hcd ⟨v, hvs⟩ hv hwt
    have hv1' : ‖(⟨v, hvs⟩ : (R ν).smSub)‖ = 1 := hv1
    exact hbd' ⟨v, hvs⟩ hLev hv1'

end prelim

section main

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem mass_low_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ ν, n1 ν ≤ q0 → ∀ (φ : (Fin (r + 1) → ℝ) → ℝ) (Bd : ℝ≥0∞), Measurable φ → (∀ y, 0 ≤ φ y) → (∀ (Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (E : ∀ ν', Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub), PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν', n1 ν' ≤ q0 → (R ν').IsE Q (E ν') ∧ Formalism.REAL.GlRel (E ν')) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd) → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd :=
  fun hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν0 φ Bd hφm hφ0 hbd w hw =>
    weightedMass_bound_lowestType_largeGap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν0 φ Bd hφm hφ0 hbd w hw

end main

end GlobalTheory.LowTypeMassGap
end
end

section

open Matrix Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.SmoothVecMod

noncomputable section

namespace GlobalTheory.CapelliCoef

variable {n : ℕ} {ε : Fin n → Bool}

lemma eabV_pair {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (L : E →L[ℂ] E') {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    L (EabV ε a b f g) = EabV ε a b (fun x => L (f x)) g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [map_add (f := _), map_smul, (rdVPair_of vector_right_derivative_extends n ε E E' L f _ g hf h1 hg).2,
    (rdVPair_of vector_right_derivative_extends n ε E E' L f _ g hf h2 hg).2]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma dsigC_unitM (ab : Fin n × Fin n) (v : H) :
    PI.DSInfCharCap.dsigC ε σ (PI.DSInfCharCap.unitM ab) v = EabV ε ab.1 ab.2 (fun x => σ x v) 1 := by
  simp only [PI.DSInfCharCap.dsigC, PI.DSInfCharCap.unitM, PI.DSInfCharCap.thetaJ, PI.PhMeasCore.dsig,
    EabV, EcV, RdV, cpart1, cpart2, Matrix.one_mul, sub_neg_eq_add, ← sub_eq_add_neg]

def freeAct (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ (smoothVec ε σ) :=
  FreeAlgebra.lift ℂ fun ab => unitAct hσ ab.1 ab.2

lemma dsigCW_eq (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (w : List (Fin n × Fin n)) (v : smoothVec ε σ) :
    PI.DSInfCharCap.dsigCW ε σ (w.map PI.DSInfCharCap.unitM) v =
      ((w.map fun ab => unitAct hσ ab.1 ab.2).prod v : smoothVec ε σ) := by
  induction w with
  | nil => rfl
  | cons ab w ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, PI.DSInfCharCap.dsigCW]
    rw [ih, dsigC_unitM, unitAct_coe]

lemma actU_eq (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (p : FreeAlgebra ℂ (Fin n × Fin n))
    (v : smoothVec ε σ) : PI.DSInfCharCap.actU ε σ p v = (freeAct hσ p v : smoothVec ε σ) := by
  have e : freeAct hσ = (MonoidAlgebra.lift ℂ _ _ (FreeMonoid.lift fun ab => unitAct hσ ab.1 ab.2)).comp
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := Fin n × Fin n)).toAlgHom := by
    ext1
    funext ab
    simp [freeAct, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [e]
  simp only [AlgHom.comp_apply, MonoidAlgebra.lift_apply, PI.DSInfCharCap.actU, dsigCW_eq hσ, Finsupp.sum,
    LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul, FreeMonoid.lift_apply]
  rfl

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def IsCoef (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P : H →L[ℂ] Wp)
    (B : Wq →ₗ[ℂ] smoothVec ε σ) (f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ g, inUJ ε g → ∀ w, f g w = P (σ g (B w))

lemma IsCoef.smooth {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) : SmoothOnGV ε f :=
  smooth_congr (PI.UnitaryGroupMassFormula.CapelliEig.coef_smoothOnGV ε σ P
    (LinearMap.toContinuousLinearMap ((smoothVec ε σ).subtype ∘ₗ B)) fun w => (B w).2)
    fun g hg => ContinuousLinearMap.ext fun w => h g hg w

lemma IsCoef.eab (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) (a b : Fin n) :
    IsCoef ε σ P (unitAct hσ a b ∘ₗ B) (EabV ε a b f) := by
  intro g hg w
  have e1 := eabV_pair (ContinuousLinearMap.apply ℂ Wp w) h.smooth a b hg
  simp only [ContinuousLinearMap.apply_apply] at e1
  rw [e1, eabV_congr (fun x hx => h x hx w) a b hg, ← eabV_pair P (B w).2 a b hg, LinearMap.comp_apply,
    unitAct_coe, rep_eabV hσ (B w).2 a b hg]

lemma IsCoef.top (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) (u : ℂ) (a b : Fin n) :
    IsCoef ε σ P (freeAct hσ (Tm (PI.DSInfCharCap.Egl n) u a b) ∘ₗ B) (Top (EabV ε) u a b f) := by
  intro g hg w
  have e := h.eab hσ a b g hg w
  have e' := h g hg w
  by_cases hab : a = b
  · subst hab
    simp [Formalism.QuantumDeterminants.Top, Tm, PI.DSInfCharCap.Egl, freeAct, Module.algebraMap_end_apply, e', e]
  · simp [Formalism.QuantumDeterminants.Top, Tm, hab, PI.DSInfCharCap.Egl, freeAct, e]

lemma IsCoef.word (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) (l : List (ℂ × Fin n × Fin n)) :
    IsCoef ε σ P (freeAct hσ (l.map fun q => Tm (PI.DSInfCharCap.Egl n) q.1 q.2.1 q.2.2).prod ∘ₗ B)
      ((l.map fun q => Top (EabV ε) q.1 q.2.1 q.2.2).foldr (fun T h => T h) f) := by
  induction l with
  | nil => simpa [Module.End.one_eq_id] using h
  | cons q l ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, map_mul, Module.End.mul_eq_comp,
      LinearMap.comp_assoc]
    exact ih.top hσ _ _ _

theorem capelli_coef : PI.UnitaryGroupMassFormula.CapelliEig.FunAct := by
  intro n ε lam Hs _ _ _ σ Wp Wq _ _ _ _ _ _ hds P Q hQ u g hg w
  have hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ := hds.2.2.1
  let B : Wq →ₗ[ℂ] smoothVec ε σ := (Q : Wq →ₗ[ℂ] Hs).codRestrict _ hQ
  have h0 : IsCoef ε σ P B (fun x => P.comp ((σ x).comp Q)) := fun _ _ _ => rfl
  have e : Q w = (B w : Hs) := rfl
  rw [e, actU_eq hσ]

  simp only [capelli, qdetOp, qminorOp, qdet, qminor, map_sum, map_mul, map_intCast, Finset.sum_apply,
  _root_.sum_apply, LinearMap.sum_apply, Submodule.coe_sum, Pi.smul_apply,
  _root_.smul_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h := h0.word hσ (List.ofFn fun k : Fin n => (u - ((k : ℕ) : ℂ), τ k, k)) g hg w
  simp only [List.map_ofFn, Function.comp_def] at h
  simp only [id]
  rw [h]
  simp [Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul ℂ]

end GlobalTheory.CapelliCoef

end
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.mass_class_eq_weight_count_alt : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E)), c1 = {Y | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ M.L.O) ∧ ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ M.L.O) ∧ (∀ a b, A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) ∧ Y = (A.transpose.map M.L.cj) * Y0 * A'} → H.Zhat f f' ∈ c1 → (∃ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t ∧ H.Zhat t.f t.f' ∈ c1) → ∃ w : ℝ, 0 < w ∧ w ≤ P.Hp ^ (3 * (r + 1) ^ 2) ∧ (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : R.RT d.1, (if ¬ LocNG.BBne (H := H) t.1 ∧ H.Zhat t.1.f t.1.f' ∈ c1 then ENNReal.ofReal (LocNG.mu P t.1) else 0)) = ENNReal.ofReal w * ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * (({Λ | LocNG.IsTermOver P d.1 (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} : Set (Submodule M.L.O V)).encard : ℝ≥0∞) := by
  first | exact @GlobalTheory.HL.LocGenMass.mass_class_eq_weight_count | exact GlobalTheory.HL.LocGenMass.mass_class_eq_weight_count | (intros; apply GlobalTheory.HL.LocGenMass.mass_class_eq_weight_count <;> assumption)
end
