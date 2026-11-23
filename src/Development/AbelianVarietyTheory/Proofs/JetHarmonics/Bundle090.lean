module

import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipSelfConjugate
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BlockProdMemAtSelfConjPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BlockProdMemChartFamilyAtPlacePairs
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle084
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle085
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.HermitianCurvature.StatementQ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle086
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle062
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.StatementQr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
public import Mathlib.RingTheory.Flat.TorsionFree
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.BesselNonvanishingReduction

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselDegree

open Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

theorem isDS_iff {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    PI.UpqRep.IsDS ε lam σ ↔ Formalism.MainNotions.S.IsDS ε lam σ := Iff.rfl

theorem haar_eq_smul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r} (hP : IsUnit P.det)
    (hH : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hν : PI.BesselPeriodGGP.IsHaarOn (GG k r) ν) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ν = c • (Formalism.REAL.muG ε).map (phi ε P) := by
  apply Gp91.GlobalTheory.BesselDegree.haar_eq_smul <;> assumption

theorem schur_fdeg : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μG : Measure (Formalism.QuantumDeterminants.Mt k r)), PI.BesselPeriodGGP.IsHaarOn (GG k r) μG → ∃ c : ℝ, 0 < c ∧ ∀ (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = c * Formalism.QuantumDeterminants.fdegHC mu) ∧ ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧ ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
  intro hy k r ε μG hμ
  have hHC : GlobalTheory.FormalDegree.HarishChandra := hy.2.2.2.2.2.2
  by_cases hQ : ∃ Q, PI.UpqRep.IsCayleyU k r ε Q
  swap
  · refine ⟨1, one_pos, fun mu R hR => absurd ?_ hQ⟩
    obtain ⟨Q, hQ, -⟩ := hR.2
    exact ⟨Q, hQ⟩
  obtain ⟨Q, hQ⟩ := hQ
  have hP : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1.1
  have hH : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r := hQ.1.2
  obtain ⟨a, ha0, hat, ha⟩ := haar_eq_smul hP hH μG hμ
  obtain ⟨c, hc, hF⟩ := hHC.chamber _ ε
  have hapos : 0 < a.toReal := ENNReal.toReal_pos ha0 hat
  have hme : MeasurableEmbedding (phi ε Q) :=
    (phi_closedEmbedding (ε := ε) Formalism.REAL.isClosedEmbeddingMatrix hP).measurableEmbedding
  refine ⟨c / a.toReal, div_pos hc hapos, fun mu R hR => ?_⟩
  have hDS := (isDS_iff _ _ _).1 ((GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R hR Q hQ)
  obtain ⟨hd, hS⟩ := hF mu hR.1 R.H _ hDS
  have hd' : 0 < c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu := by
    rw [div_mul_eq_mul_div]; exact div_pos hd hapos
  have key : ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧ ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
    intro v w v' w'
    obtain ⟨h1, h2⟩ := hS v w v' w'
    rw [ha]
    constructor
    · refine Integrable.smul_measure ?_ hat
      rw [hme.integrable_map_iff]
      exact h1
    · rw [integral_smul_measure, hme.integral_map]
      have h3 : ∫ g, ⟪w, R.σ (Matrix.of (phi ε Q g)) v⟫_ℂ * star ⟪w', R.σ (Matrix.of (phi ε Q g)) v'⟫_ℂ
          ∂(Formalism.REAL.muG ε) = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := h2
      rw [h3, div_mul_eq_mul_div, Complex.ofReal_div, div_div_eq_mul_div, Complex.real_smul]
      ring
  exact ⟨fun w hw => Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq hd' key hw, key⟩

end GlobalTheory.BesselDegree
end
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem wigMap_comp : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (V₃ : Type) [NormedAddCommGroup V₃] [InnerProductSpace ℂ V₃] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π₁ : Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (π₃ : Mx k r → (V₃ →L[ℂ] V₃)) (d e : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (V₂ →L[ℂ] V₁)) (A' : (Fin (2 * r + k + 1) → ℂ) → (V₃ →L[ℂ] V₂)), GlobalTheory.WigSh.WigMap k r z π₂ π₁ d A → GlobalTheory.WigSh.WigMap k r z π₃ π₂ e A' → GlobalTheory.WigSh.WigMap k r z π₃ π₁ (d + e) (fun ω => (A ω).comp (A' ω)) := by
  intro V₁ _ _ V₂ _ _ V₃ _ _ k r z π₁ π₂ π₃ d e A A' hA hA'
  obtain ⟨⟨t, q, L, hq, hL⟩, h2, h3, h4⟩ := hA
  obtain ⟨⟨t', q', L', hq', hL'⟩, h2', h3', h4'⟩ := hA'
  refine ⟨⟨t * t', fun i => q (finProdFinEquiv.symm i).1 * q' (finProdFinEquiv.symm i).2,
    fun i => (L (finProdFinEquiv.symm i).1).comp (L' (finProdFinEquiv.symm i).2), ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i
    exact (MvPolynomial.totalDegree_mul _ _).trans (add_le_add (hq _) (hq' _))
  · intro ω
    rw [Equiv.sum_comp finProdFinEquiv.symm (fun p : Fin t × Fin t' =>
      MvPolynomial.eval (Sum.elim ω (fun j => star (ω j))) (q p.1 * q' p.2) • (L p.1).comp (L' p.2)),
      Fintype.sum_prod_type]
    show (A ω).comp (A' ω) = _
    rw [hL ω, hL' ω]
    ext x
    simp only [ContinuousLinearMap.comp_apply, sum_apply, ContinuousLinearMap.smul_apply,
      map_sum, map_smul, Finset.smul_sum, map_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_comm, smul_smul]
  · intro h hh ω
    show ((A (h *ᵥ ω)).comp (A' (h *ᵥ ω))).comp (π₃ h) = (π₁ h).comp ((A ω).comp (A' ω))
    rw [ContinuousLinearMap.comp_assoc, h2' h hh, ← ContinuousLinearMap.comp_assoc, h2 h hh,
      ContinuousLinearMap.comp_assoc]
  · intro s ω
    show (A ((s : ℂ) • ω)).comp (A' ((s : ℂ) • ω)) = ((s : ℂ) ^ (d + e)) • (A ω).comp (A' ω)
    rw [h3, h3', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul, pow_add]
  · intro ω hω hz
    show ‖(A ω).comp (A' ω)‖ ^ 2 ≤ _
    have a := h4 ω hω hz
    have b := h4' ω hω hz
    calc ‖(A ω).comp (A' ω)‖ ^ 2 ≤ (‖A ω‖ * ‖A' ω‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.opNorm_comp_le _ _) 2
      _ = ‖A ω‖ ^ 2 * ‖A' ω‖ ^ 2 := mul_pow _ _ _
      _ ≤ _ := by
          rw [pow_add]
          exact mul_le_mul a b (sq_nonneg _) ((sq_nonneg _).trans a)

end GlobalTheory.WigSh
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh


open Matrix in
theorem _root_.GlobalTheory.WigSh.wigMap_zero_of_contraction : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π₁ : _root_.Formalism.FourierDecayAlt.Q.Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : _root_.Formalism.FourierDecayAlt.Q.Mx k r → (V₂ →L[ℂ] V₂)) (φ : V₂ →L[ℂ] V₁), (∀ v, ‖φ v‖ ≤ ‖v‖) → (∀ h ∈ _root_.Formalism.QuantumDeterminants.UWset k r z, ∀ v, φ (π₂ h v) = π₁ h (φ v)) → _root_.GlobalTheory.WigSh.WigMap k r z π₂ π₁ 0 (fun _ => φ) := by
  intro V₁ _ _ V₂ _ _ k r z π₁ π₂ φ hφ heqv
  refine ⟨⟨1, fun _ => 1, fun _ => φ, fun _ => by simp, fun ω => by simp⟩,
    fun h hh ω => ?_, fun t ω => by simp, fun ω _ _ => ?_⟩
  · ext v
    exact heqv h hh v
  · have hle : ‖φ‖ ≤ 1 := φ.opNorm_le_bound zero_le_one (fun v => by simpa using hφ v)
    rw [pow_zero]
    exact pow_le_one₀ (norm_nonneg _) hle

end GlobalTheory.WigSh
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth.EigExt

theorem res_surjective_of_extends {R O : Type} [CommRing R] [CommRing O] (ι : R →+* O) {d s : ℕ}
    (u : Fin s → Fin d → R) (w : Fin d → Fin d → R) (emb : Fin s ↪ Fin d) (hw : ∀ i, w (emb i) = u i)
    (hb : ∀ v : Fin d → R, ∃! a : Fin d → R, ∀ j, ∑ k, a k * w k j = v j) :
    Function.Surjective (res (fun i j => ι (u i j))) := by
  classical
  have h1 : IsUnit (Matrix.of w) := by
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    intro v
    obtain ⟨a, ha, -⟩ := hb v
    exact ⟨a, funext fun j => ha j⟩
  have h2 : IsUnit (ι.mapMatrix (Matrix.of w)) := h1.map _
  rw [← Matrix.mulVec_surjective_iff_isUnit] at h2
  intro g
  obtain ⟨f, hf⟩ := h2 (Function.extend emb g 0)
  refine ⟨f, funext fun i => ?_⟩
  have h3 := congrFun hf (emb i)
  rw [emb.injective.extend_apply] at h3
  rw [← h3]
  show ∑ j, ι (u i j) * f j = ∑ j, ι (w (emb i) j) * f j
  rw [hw]

theorem ι_injective {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) : Function.Injective X.ι := by
  intro a b h
  apply IsFractionRing.injective T.V T.Fr
  apply X.ιF.injective
  rw [X.comp, X.comp, h]

theorem flat {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) :
    letI := X.ι.toAlgebra; Module.Flat T.V X.O := by
  letI := X.ι.toAlgebra
  haveI : IsDomain X.O := Function.Injective.isDomain (algebraMap X.O X.C) X.ints.hom_inj
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  have hx' : X.ι a * x = 0 := hx
  have ha' : X.ι a ≠ 0 := fun h => nonZeroDivisors.ne_zero ha (ι_injective X (h.trans (map_zero _).symm))
  exact (mul_eq_zero.1 hx').resolve_left ha'

theorem linPart_add {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
    (Ch : IntegralChartA3 Xo c T io y) (a b : 𝓞 E) :
    ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (Ch.actT (a + b)) = ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (Ch.actT a) + ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (Ch.actT b) := by
  letI := io.toAlgebra
  have key : ∀ a i j, ReciprocityTheory.ChartRestriction.G.TB.dAct T.Fr Ch.ch.B a i j = algebraMap T.V T.Fr (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart (Ch.actT a) i j) := by
    intro a i j
    show MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1)
      (MvPowerSeries.map (algebraMap T.Fr T.Fr) (Ch.ch.B.A.act a i)) = _
    rw [MvPowerSeries.coeff_map, Ch.gen.1.2.1 a i, MvPowerSeries.coeff_map]
    rfl
  ext i j
  apply IsFractionRing.injective T.V T.Fr
  rw [Matrix.add_apply, map_add (f := _), ← key, ← key, ← key, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add, Matrix.add_apply]

end GlobalTheory.CharDepth.EigExt


open GlobalTheory.CharDepth.EigExt in
theorem GlobalTheory.CharDepth.isEigBasis_valExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (τO : (E →+* ℂ) → (𝓞 E →+* X.O)), IsTypes X io τO → ∀ τ : E →+* ℂ, IsEigBasis (fun a i => MvPowerSeries.map X.ι (Ch.actT a i)) (τO τ) (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j)) ∧ Function.Surjective (res (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j))) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch p _ X τO hτ τ
  constructor
  · obtain ⟨τT, hT, hT', -⟩ := GlobalTheory.T.exists_cmType_embeddings_into_valuation_ring E H l c T io p X
    have he : τO τ = X.ι.comp (τT τ) := by
      ext a
      apply X.ints.hom_inj
      rw [hτ τ a]
      exact (hT' τ a).symm
    letI := X.ι.toAlgebra
    haveI := flat X
    rw [he]
    exact GlobalTheory.T.isEigenBasis_map_flat_baseChange T.V X.O (𝓞 E) _ _ Ch.actT (linPart_add Ch) (τT τ) _
      (GlobalTheory.T.integral_chart_directions_isEigenBasis E H Dw l Xo c T io y Ch τ (τT τ) (hT τ))
  · obtain ⟨⟨w, emb, hw, hb⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y Ch τ
    exact res_surjective_of_extends X.ι _ w emb hw hb
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.blockProd_mem_at_selfConj_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (Orb : Type) [Fintype Orb] (lab : LabS E Orb), ArithS V io ι lab → Function.Surjective (fun x : Orb × ZMod 2 => lab.tau x.1 x.2) → lab.RankOK Dw → lab.j' < lab.n → ∀ p : ∀ o, SelfData Y 2 (lab.II Dw o), IsSelfOf C3 ι Y lab p → ∀ (Hy : ∀ o, (Y.rawSelf (p o)).Hyps V) (F : ∀ o, RF.Flag ((Y.rawSelf (p o)).rowData (Hy o))), (∀ o g s q, (((F o).en g s q).2 : ℕ) = q) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (N n : ℕ) (pl : Fin N × Fin 2 ↪ Fin n), RF.BlockMembershipSelfConjugate (fun o => (Y.rawSelf (p o)).rowData (Hy o)) N F (imgFamS Y p (chartLetterSystem C3 V ι a) pl) (fun o s => gap (Dw.mult (lab.tau o s)) fun i => a (lab.tau o s, i)) := by
  first | exact @GlobalTheory.SelfConjMem.blkMemC_self | exact GlobalTheory.SelfConjMem.blkMemC_self | (intros; apply GlobalTheory.SelfConjMem.blkMemC_self <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.blockProd_mem_chartFamily_at_place_pairs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab), Function.Surjective (fun x : Orb × Fin 2 × ZMod d => lab.tau x.1 x.2.1 x.2.2) → lab.RankOK Dw → lab.j' < lab.n → ∀ (Hy : ∀ o, (Y.raw (pairOfLab ha hg o)).Hyps V) (F : ∀ o, RF.Flag (RF.rd Y (pairOfLab ha hg) Hy o)), (∀ o g s q, (((F o).en g s q).2 : ℕ) = q) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ n : ℕ, RF.BlockMembershipChart Y (pairOfLab ha hg) Hy (chartLetterSystem C3 V ι a) n F Finset.univ (fun o g s => gap (Dw.mult (lab.tau o g s)) fun i => a (lab.tau o g s, i)) := by
  first | exact @GlobalTheory.MemPair.blkMemSt_pair | exact GlobalTheory.MemPair.blkMemSt_pair | (intros; apply GlobalTheory.MemPair.blkMemSt_pair <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.cpSeriesCoeffNormBounded_ring_laws : ∀ (q : ℕ) [Fact q.Prime], (∀ (f g : ℂ_[q]⟦X⟧) (A B : ℝ), Bd A f → Bd B g → Bd (max A B) (f + g) ∧ Bd (A * B) (f * g)) ∧ (∀ (f h : ℂ_[q]⟦X⟧) (A : ℝ), Bd A f → Bd 1 h → constantCoeff h = 0 → Bd A (f.subst h)) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bd 1 f → ‖constantCoeff f‖ = 1 → f * g = 1 → Bd 1 g) ∧ (∀ (f g : ℂ_[q]⟦X⟧) (B : ℝ), Bdd f → Bdd g → Bd B (f * g) → ∀ i j, ‖coeff i f‖ * ‖coeff j g‖ ≤ B) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bdd f → Bdd g → f * g = 1 → constantCoeff f = 1 → Bd 1 f ∧ Bd 1 g) ∧ (∀ (f v : ℂ_[q]⟦X⟧) (k : ℕ) (B : ℝ), Bd 1 v → ‖constantCoeff v‖ = 1 → Bd B (X ^ k * v * f) → Bd B f) := by
  first | exact @GlobalTheory.MomOne.sup_norm_laws | exact GlobalTheory.MomOne.sup_norm_laws | (intros; apply GlobalTheory.MomOne.sup_norm_laws <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.exists_imagQuadOrder_pair_and_evenTheta : ∀ d : ℕ, d.Prime → d % 16 = 7 → (∃ L : PeriodPair, IsOK d L ∧ L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = discr d) ∧ ∃ θ : ℂ → ℂ, IsTh d θ := by
  first | exact @GlobalTheory.MomOne.exists_pair_and_isTh | exact GlobalTheory.MomOne.exists_pair_and_isTh | (intros; apply GlobalTheory.MomOne.exists_pair_and_isTh <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.germ_boxProduct_eq_prod_germs : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → BoxGermSt := by
  first | exact @GlobalTheory.PowGerm.boxGermSt_holds | exact GlobalTheory.PowGerm.boxGermSt_holds | (intros; apply GlobalTheory.PowGerm.boxGermSt_holds <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselDecay

theorem gN_mul_le' {k r : ℕ} (a b : Mx k r) : B.gN (a * b) ≤ B.gN a * B.gN b := by
  exact PI.PolynomialProperness.GN.gN_mul_le a b

theorem gN_pos' {k r : ℕ} {a : Mx k r} (ha : a ∈ GG k r) : 0 < B.gN a := by
  exact PI.PolynomialProperness.GN.gN_pos ha

theorem sum_nonneg' {α : Type} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (L : List α) : 0 ≤ (L.map f).sum := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp ha
  exact hf w

theorem one_le_aOf {k r : ℕ} {h : ℝ} (hg : GapOK k r h) : 1 ≤ aOf r h := by
  have h4 := hg.2.2.2
  have : 0 ≤ AG k r := by unfold AG; positivity
  have : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  linarith

theorem decay_TK : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → ∀ v ∈ R.TK, ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧ ∀ w ∈ R.sm, ∀ x ∈ GG k r, ‖⟪v, R.σ x w⟫_ℂ‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum * B.gN x ^ (1 - aOf r h) := by
  intro H k r ε mu h R hR hgap hok v hv
  have hdec : DecInf := H.1.2.1
  have ha := one_le_aOf hok
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨g, hg, v₀, hv₀, rfl⟩ := hv
    obtain ⟨C, Ws, hWs, hb⟩ := hdec k r ε mu h R.H R.σ hR.1 hR.2 hgap hok v₀ hv₀
    refine ⟨|C| * B.gN g ^ (aOf r h - 1), Ws, hWs, fun w hw x hx => ?_⟩
    obtain ⟨hi, hgi, hig⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hg
    have hy : g⁻¹ * x ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hi hx
    have hx' : x = g * (g⁻¹ * x) := by rw [← Matrix.mul_assoc, hgi, Matrix.one_mul]
    have hunit := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hR.2).2
    have hiso : ∀ a b, ⟪R.σ g a, R.σ g b⟫_ℂ = ⟪a, b⟫_ℂ :=
      (LinearMap.norm_map_iff_inner_map_map ((R.σ g : R.H →L[ℂ] R.H) : R.H →ₗ[ℂ] R.H)).1 (hunit g hg)
    have e : ⟪R.σ g v₀, R.σ x w⟫_ℂ = ⟪v₀, R.σ (g⁻¹ * x) w⟫_ℂ := by
      rw [← hiso v₀]
      congr 1
      conv_lhs => rw [hx', Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hR.2 hg hy]
      rfl
    rw [e]
    have h1 := hb w hw _ hy
    set S := (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum with hS
    have hS0 : 0 ≤ S := sum_nonneg' _ (fun _ => norm_nonneg _) _
    have pg := gN_pos' hg
    have px := gN_pos' hx
    have py := gN_pos' hy
    have hle : B.gN x ≤ B.gN g * B.gN (g⁻¹ * x) := by
      conv_lhs => rw [hx']
      exact gN_mul_le' _ _
    have h2 : (B.gN g * B.gN (g⁻¹ * x)) ^ (1 - aOf r h) ≤ B.gN x ^ (1 - aOf r h) :=
      Real.rpow_le_rpow_of_nonpos px hle (by linarith)
    rw [Real.mul_rpow pg.le py.le] at h2
    have h3 : B.gN g ^ (aOf r h - 1) * B.gN g ^ (1 - aOf r h) = 1 := by
      rw [← Real.rpow_add pg]; simp
    have pg' : 0 < B.gN g ^ (aOf r h - 1) := Real.rpow_pos_of_pos pg _
    have h4 : B.gN (g⁻¹ * x) ^ (1 - aOf r h) ≤ B.gN g ^ (aOf r h - 1) * B.gN x ^ (1 - aOf r h) := by
      calc B.gN (g⁻¹ * x) ^ (1 - aOf r h)
          = B.gN g ^ (aOf r h - 1) * (B.gN g ^ (1 - aOf r h) * B.gN (g⁻¹ * x) ^ (1 - aOf r h)) := by
            rw [← mul_assoc, h3, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 pg'.le
    calc _ ≤ C * S * B.gN (g⁻¹ * x) ^ (1 - aOf r h) := h1
      _ ≤ |C| * S * B.gN (g⁻¹ * x) ^ (1 - aOf r h) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hS0)
            (Real.rpow_pos_of_pos py _).le
      _ ≤ |C| * S * (B.gN g ^ (aOf r h - 1) * B.gN x ^ (1 - aOf r h)) :=
          mul_le_mul_of_nonneg_left h4 (mul_nonneg (abs_nonneg C) hS0)
      _ = _ := by ring
  | zero => exact ⟨0, [], by simp, fun w _ x _ => by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨C, Ws, hWs, hb⟩ := hu
    obtain ⟨C', Ws', hWs', hb'⟩ := hv
    refine ⟨|C| + |C'|, Ws ++ Ws', fun W hW => (List.mem_append.1 hW).elim (hWs W) (hWs' W),
      fun w hw x hx => ?_⟩
    have h1 := hb w hw x hx
    have h2 := hb' w hw x hx
    rw [List.map_append, List.sum_append, inner_add_left]
    set S := (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum with hS
    set S' := (Ws'.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum with hS'
    have hS0 : 0 ≤ S := sum_nonneg' _ (fun _ => norm_nonneg _) _
    have hS0' : 0 ≤ S' := sum_nonneg' _ (fun _ => norm_nonneg _) _
    have px : 0 ≤ B.gN x ^ (1 - aOf r h) := (Real.rpow_pos_of_pos (gN_pos' hx) _).le
    have h3 : C * S + C' * S' ≤ (|C| + |C'|) * (S + S') := by
      have a1 := mul_le_mul_of_nonneg_right (le_abs_self C) hS0
      have a2 := mul_le_mul_of_nonneg_right (le_abs_self C') hS0'
      have a3 := mul_nonneg (abs_nonneg C) hS0'
      have a4 := mul_nonneg (abs_nonneg C') hS0
      nlinarith
    calc _ ≤ ‖⟪u, R.σ x w⟫_ℂ‖ + ‖⟪v, R.σ x w⟫_ℂ‖ := norm_add_le _ _
      _ ≤ (C * S + C' * S') * B.gN x ^ (1 - aOf r h) := by rw [add_mul]; exact add_le_add h1 h2
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 px
  | smul c v _ hv =>
    obtain ⟨C, Ws, hWs, hb⟩ := hv
    refine ⟨‖c‖ * C, Ws, hWs, fun w hw x hx => ?_⟩
    rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc, mul_assoc, ← mul_assoc C]
    exact mul_le_mul_of_nonneg_left (hb w hw x hx) (norm_nonneg c)

end GlobalTheory.BesselDecay
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.dual_tensor_cayley_compatible : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)) (F : ∀ s, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (RI s).smSub), (∀ s, (RI s).IsDS ε (muI s)) → TensRaw dualM R RI io pr → IsUnit Q → R.IsE Q E → (∀ s, (RI s).IsE Q (F s)) → ∃ (io' : ∀ s, (RI s).smSub →ₗ[ℂ] (Fin (2 * r + k + 1) → R.smSub)) (pr' : ∀ s, (Fin (2 * r + k + 1) → R.smSub) →ₗ[ℂ] (RI s).smSub), (∀ s a b y, io' s (F s a b y) = dualTens E a b (io' s y)) ∧ (∀ s a b x, pr' s (dualTens E a b x) = F s a b (pr' s x)) ∧ (∀ x, ∑ s, io' s (pr' s x) = x) ∧ (∀ s y, pr' s (io' s y) = y) ∧ (∀ s t, s ≠ t → ∀ y, pr' s (io' t y) = 0) ∧ (∀ s y d, ((io' s y d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • io s c (y : (RI s).H)) ∧ ∀ s x, ((pr' s x : (RI s).smSub) : (RI s).H) = ∑ c, pr s c (∑ d, Q d c • ((x d : R.smSub) : R.H)) := by
  first | exact @GlobalTheory.RawTens.rawTens | exact GlobalTheory.RawTens.rawTens | (intros; apply GlobalTheory.RawTens.rawTens <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.projector_entry_value_under_linear_functional : ∀ (M Wp : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → ∀ (mu : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (Pop : Fin k → Fin k → Wp → Wp), Function.Injective mu → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → (∀ i j v, l (E ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) v) = Pop i j (l v)) → (∀ (w : ℂ) (x : Wp), Formalism.FourierDecayAlt.Q.qmF Pop id id w x = (∏ i ∈ Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ))) • x) → ∀ s, ∃ c : ℂ, ‖c‖ = (if r = 0 then 1 else τ ^ 2) * ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) ∧ ∀ (v : M) (y : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → M), (∀ t, splitCas E (y t) = ((-mu t + (1 - (((2 * r + k + 1) : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∑ t, y t = Pi.single (Fin.last (2 * r + k)) v → l (y s (if r = 0 then Fin.last (2 * r + k) else 0)) = c • l v := by
  first | exact @GlobalTheory.capelli_projector_entry_value | exact GlobalTheory.capelli_projector_entry_value | (intros; apply GlobalTheory.capelli_projector_entry_value <;> assumption)
end
