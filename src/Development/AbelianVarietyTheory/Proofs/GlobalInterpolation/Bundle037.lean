module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle014
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle022
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsOfFixedInt
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLargeVonMangoldtLogPowerSeriesNearZero
public import Formalism.GL3MeanSquares.HookFormulaTorsion.GlobalBoundRefinements
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle032
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle035
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle033
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal NNReal

namespace GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique

theorem normaliseQuotientClause : NormaliseQuotientClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH hG hH' dg _ ν _
  obtain ⟨⟨μ₀, hμ₀⟩, huniq⟩ := GlobalTheory.T.quotientInvariantMeasure_exists_unique_unimodular G H hH hG hH'
  obtain ⟨dg₀, ⟨hdg₀, hF₀⟩, -⟩ := GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH ν μ₀ hμ₀
  set c : ℝ≥0 := haarScalarFactor dg dg₀ with hc
  have hcpos : 0 < c := haarScalarFactor_pos_of_isHaarMeasure dg dg₀
  have hdg : dg = c • dg₀ := isMulLeftInvariant_eq_smul dg dg₀
  have hR : IsInvariantRadon H (c • μ₀) := by
    haveI := hμ₀.finiteOnCompacts
    haveI := hμ₀.invariant
    refine ⟨?_, inferInstance, ⟨fun g s hs => ?_⟩⟩
    · intro h
      apply hμ₀.ne_zero
      have : c⁻¹ • (c • μ₀) = μ₀ := by
        rw [smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
      rw [← this, h, smul_zero]
    · simp only [Measure.coe_nnreal_smul_apply]
      rw [SMulInvariantMeasure.measure_preimage_smul g hs]
  have hF : QuotientFormula H dg ν (c • μ₀) := by
    intro f hf
    obtain ⟨h1, h2⟩ := hF₀ f hf
    refine ⟨h1, ?_⟩
    rw [hdg, lintegral_smul_measure, lintegral_smul_measure, h2]
  refine ⟨c • μ₀, ⟨hR, hF⟩, ?_⟩
  rintro μ ⟨hμ, hμF⟩
  obtain ⟨d, -, hd⟩ := huniq _ _ hR hμ
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have hKm : MeasurableSet (K : Set G) := K.isCompact.measurableSet
  have hfm : Measurable ((K : Set G).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hKm
  have e1 := (hF _ hfm).2
  have e2 := (hμF _ hfm).2
  rw [hd, lintegral_smul_measure, ← e1, lintegral_indicator_const hKm, one_mul] at e2
  have hpos : dg K ≠ 0 := (measure_pos_of_nonempty_interior dg K.interior_nonempty).ne'
  have hfin : dg K ≠ ∞ := K.isCompact.measure_lt_top.ne
  have hd1 : d = 1 := by
    have : (d : ℝ≥0∞) * dg K = 1 * dg K := by
      rw [one_mul]; exact e2.symm
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).mp this
  rw [hd, hd1, one_smul]

end GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique
end

section

namespace GlobalTheory.UnramSelfDualClosed

theorem selfDualLatticeLemmas : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.SelfDualLatticeLemmas :=
  GlobalTheory.SelfDualLatticeCompare.selfDualLattices_iff.1 GlobalTheory.UnramSelfDual.selfDualLattices

end GlobalTheory.UnramSelfDualClosed
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

theorem _root_.GlobalTheory.T.finprod_localDifferentIdealNorm_eq_discr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → (Function.mulSupport (normDifferentV F)).Finite ∧ ((∏ᶠ v, normDifferentV F v : ℕ) : ℝ) = absDiscr F ∧ absDiscr F = (2 * Formalism.HermitianLatticesTheory.vInv E) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  first | exact @GlobalTheory.LocalDifferentProduct.prod_normDifferentV | exact GlobalTheory.LocalDifferentProduct.prod_normDifferentV | (intros; apply GlobalTheory.LocalDifferentProduct.prod_normDifferentV <;> assumption)
end

section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.latticeJetsAreBoundedMoments_of_span_imagQuadratic : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (d : ℕ) (ω : ℂ_[q]) (Λ : AddSubgroup V) (κ : Type) [Fintype κ] (b : κ → V) (G : V → ℂ), d.Prime → d % 16 = 7 → Split d q → (∀ x ∈ Λ, ∃ s : ℕ, Nat.Coprime s q ∧ ∃ c : κ → ℂ, (∀ i, InOK d (c i)) ∧ (s : ℂ) • x = ∑ i, c i • b i) → MomInt ι (fun i => ι.symm ω • b i) G → LatInt ι ω Λ G := by
  first | exact @GlobalTheory.MomN.latInt_of_span | exact GlobalTheory.MomN.latInt_of_span | (intros; apply GlobalTheory.MomN.latInt_of_span <;> assumption)
end

section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ω : ℂ_[q]) (Λ : AddSubgroup V), (∀ (m : Type) [Fintype m] (G : m → V → ℂ), (∀ j, ContDiff ℂ ⊤ (G j)) → (∀ j, LatInt ι ω Λ (G j)) → LatInt ι ω Λ fun z => ∏ j, G j z) ∧ ∀ (m : Type) (s : Finset m) (c : m → ℂ) (G : m → V → ℂ), (∀ j ∈ s, ContDiff ℂ ⊤ (G j)) → (∀ j ∈ s, ‖ι (c j)‖ ≤ 1) → (∀ j ∈ s, LatInt ι ω Λ (G j)) → LatInt ι ω Λ fun z => ∑ j ∈ s, c j * G j z := by
  first | exact @GlobalTheory.MomN.latInt_prod_sum | exact GlobalTheory.MomN.latInt_prod_sum | (intros; apply GlobalTheory.MomN.latInt_prod_sum <;> assumption)
end

section

open GlobalTheory.MomN

theorem _root_.GlobalTheory.T.mahlerJetCoefficient_mul_of_disjoint_support : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ι' : Type) [Fintype ι'] [DecidableEq ι'] (u : ι' → V) (F H : V → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ H → ∀ (S T : Finset ι'), Disjoint S T → (∀ k : ι' → ℕ, (∃ p, p ∉ S ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u F k = 0) → (∀ k : ι' → ℕ, (∃ p, p ∉ T ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u H k = 0) → (∀ N : ι' → ℕ, (∃ p, p ∉ S ∪ T ∧ N p ≠ 0) → GlobalTheory.MomN.mahler u (fun z => F z * H z) N = 0) ∧ (∀ N : ι' → ℕ, (∀ p, p ∉ S ∪ T → N p = 0) → GlobalTheory.MomN.mahler u (fun z => F z * H z) N = GlobalTheory.MomN.mahler u F (fun p => if p ∈ S then N p else 0) * GlobalTheory.MomN.mahler u H (fun p => if p ∈ T then N p else 0)) := by
  first | exact @GlobalTheory.mahler_mul_of_disjoint_support | exact GlobalTheory.mahler_mul_of_disjoint_support | (intros; apply GlobalTheory.mahler_mul_of_disjoint_support <;> assumption)
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.exists_large_vonMangoldtLogPowerSeries_near_zero : ∃ A C r₀ : ℝ, 1 ≤ A ∧ 0 < C ∧ 0 < r₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (τ r L : ℝ) (K : ℕ) (ρ : ℂ), (χ ≠ 1 ∨ 2 ≤ |τ|) → Real.log (q * (|τ| + 2)) ≤ L → 1 / L ≤ r → r ≤ r₀ → C * r * L ≤ K → LFunction χ ρ = 0 → ‖ρ - (1 + τ * I)‖ ≤ r → ∃ k : ℕ, K ≤ k ∧ k ≤ 2 * K ∧ 1 / (A * r) ^ (k + 1) ≤ ‖derSeries (fun n : ℕ => χ (n : ZMod q)) k ((1 + r : ℝ) + τ * I)‖ := by
  first | exact @GlobalTheory.NearZeroDeriv.exists_large_derSeries | exact GlobalTheory.NearZeroDeriv.exists_large_derSeries | (intros; apply GlobalTheory.NearZeroDeriv.exists_large_derSeries <;> assumption)
end

section

open Finset Formalism.HermitianLattices.GL2PrimeSums

namespace GlobalTheory.Lin


open Finset in
theorem _root_.GlobalTheory.Lin.primesAPInterval_of_primesRel (h : _root_.GlobalTheory.Lin.PrimesRel) :
    ∃ C₀ Cr cr c : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < c ∧ _root_.Formalism.HermitianLattices.GL2PrimeSums.PrimesAPInterval C₀ Cr cr c := by
  unfold _root_.GlobalTheory.Lin.PrimesRel at h
  obtain ⟨c₁, c₂, c₃, CA, cS, hc₁, hc₁8, hc₂, hc₃, hCA, hcS, hmain⟩ := h
  set cr := min c₃ (Real.sqrt c₃) with hcr
  have hcr0 : 0 < cr := lt_min hc₃ (Real.sqrt_pos.mpr hc₃)
  have hdata : _root_.Formalism.HermitianLattices.GlobalBoundRefinements.PrimeCountAsymptoticInProgressions c₂ CA cr cS := by
    unfold _root_.Formalism.HermitianLattices.GlobalBoundRefinements.PrimeCountAsymptoticInProgressions
    intro m a hm ha
    haveI : NeZero m := ⟨by omega⟩
    obtain ⟨huniq, hgap, hcount⟩ := hmain m hm
    have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
    have hlogm : 0 < Real.log m := Real.log_pos hm1
    have hlog4m : Real.log m ≤ Real.log (4 * m) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog3 : 1 < Real.log m := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      have : (3 : ℝ) ≤ m := by exact_mod_cast hm
      linarith [Real.exp_one_lt_d9]

    have hterm : ∃ (θ : ℤ) (β : ℝ), θ ∈ ({-1, 0, 1} : Set ℤ) ∧
        (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cS / ((4 * (m : ℝ)) ^ 2 * Real.log (4 * m)) ≤ 1 - β) ∧
        _root_.GlobalTheory.Lin.ExcData c₁ m a θ β := by
      by_cases hex : ∃ (χ : DirichletCharacter ℂ m) (β : ℝ), _root_.GlobalTheory.Lin.IsExc c₁ χ β
      · obtain ⟨χ, β, hχ⟩ := hex
        have hunit : IsUnit (a : ZMod m) := (ZMod.isUnit_iff_coprime a m).mpr ha
        have hsq : χ (a : ZMod m) ^ 2 = 1 := by
          rw [← MulChar.pow_apply' χ (by norm_num), hχ.1, MulChar.one_apply hunit]
        obtain ⟨θ, hθ, hθmem⟩ : ∃ θ : ℤ, χ (a : ZMod m) = θ ∧ θ ∈ ({-1, 0, 1} : Set ℤ) := by
          have hsq' : χ (a : ZMod m) * χ (a : ZMod m) = 1 := by rw [← pow_two]; exact hsq
          rcases mul_self_eq_one_iff.mp hsq' with h1 | h1
          · exact ⟨1, by simp [h1], by simp⟩
          · exact ⟨-1, by simp [h1], by simp⟩
        refine ⟨θ, β, hθmem, fun _ => ⟨?_, hχ.2.2.1, ?_⟩, Or.inr ⟨χ, hχ, hθ⟩⟩
        · have h1 := hχ.2.1
          have : c₁ / Real.log m ≤ 1 / 2 := by
            rw [div_le_iff₀ hlogm]
            linarith
          linarith
        · refine le_trans ?_ (hgap χ β hχ)
          apply div_le_div_of_nonneg_left hcS.le (by positivity)
          have : (m : ℝ) ^ 2 ≤ (4 * m) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity)
            linarith
          exact mul_le_mul this hlog4m hlogm.le (by positivity)
      · refine ⟨0, 1 / 2, by simp, fun h0 => absurd rfl h0, Or.inl ⟨rfl, fun χ β hχ => hex ⟨χ, β, hχ⟩⟩⟩
    obtain ⟨θ, β, hθmem, hβ, hdat⟩ := hterm
    refine ⟨θ, β, fun _ => 0, hθmem, hβ,
      fun _ => ⟨le_rfl, mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))⟩, ?_⟩
    intro Y hY
    have hY1 : (m : ℝ) ^ c₂ ≤ Y := by
      refine le_trans ?_ hY
      exact Real.rpow_le_rpow (by positivity) (by linarith) hc₂.le
    have hb := hcount a θ β ha hdat Y hY1
    have hY1' : 1 ≤ Y := le_trans (Real.one_le_rpow (by linarith) hc₂.le) hY1
    have hL : 0 ≤ Real.log Y := Real.log_nonneg hY1'
    have hpos : 0 < CA * (Real.exp (-c₃ * Real.log Y / Real.log m) +
        Real.exp (-√(c₃ * Real.log Y))) := by
      positivity
    have hE : 0 ≤ _root_.Formalism.HermitianLattices.GL2PrimeSums.Emain θ β Y :=
      (mul_nonneg_iff_of_pos_left hpos).mp ((abs_nonneg _).trans hb)
    have h1 : Real.exp (-c₃ * Real.log Y / Real.log m) ≤
        Real.exp (-cr * Real.log Y / Real.log (4 * m)) := by
      rw [Real.exp_le_exp, neg_mul, neg_mul, neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right (min_le_left _ _) hL)
        hlogm hlog4m
    have h2 : Real.exp (-√(c₃ * Real.log Y)) ≤ Real.exp (-cr * √(Real.log Y)) := by
      rw [Real.exp_le_exp, neg_mul, neg_le_neg_iff, Real.sqrt_mul hc₃.le]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
    simp only [add_zero]
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ hE)
    unfold _root_.Formalism.HermitianLattices.GL2PrimeSums.rhoErr
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hCA.le) (mul_le_mul_of_nonneg_left h2 hCA.le)
  obtain ⟨C₀', c, hC₀', hc, hint⟩ := _root_.Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalImpliesProgressions_statement _root_.Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalLowerBound c₂ CA cr cS hc₂ hCA hcr0 hcS hdata
  exact ⟨C₀', CA, cr, c, hC₀', hCA, hcr0, hc, hint⟩

end GlobalTheory.Lin
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.glMatrixUnit_pow_commutator_and_trace_central : ∀ (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A), GlRel E → ∀ k : ℕ, (∀ a b c d, E a b * (E ^ k) c d - (E ^ k) c d * E a b = (if b = c then (E ^ k) a d else 0) - (if d = a then (E ^ k) c b else 0)) ∧ ∀ a b, E a b * (E ^ k).trace = (E ^ k).trace * E a b := by
  first | exact @GlobalTheory.Alc.glRel_pow_comm | exact GlobalTheory.Alc.glRel_pow_comm | (intros; apply GlobalTheory.Alc.glRel_pow_comm <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc.HighestVec

theorem weight_rowW_apply {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type, rowDeg]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp [rowW]
  · intro b _ hb
    refine Finset.sum_eq_zero fun s _ => ?_
    simp [rowW, Ne.symm hb]
  · simp

def height (N : ℕ) (μ : Fin N → ℕ) : ℕ := ∑ a : Fin N, (N - a.val) * μ a

theorem height_add (N : ℕ) (μ ν : Fin N → ℕ) : height N (μ + ν) = height N μ + height N ν := by
  simp [height, mul_add, Finset.sum_add_distrib]

theorem height_single (N : ℕ) (a : Fin N) : height N (Pi.single a 1) = N - a.val := by
  simp [height, Pi.single_apply]

theorem height_lt_swap (N : ℕ) (μ : Fin N → ℕ) (a b : Fin N) (hab : a < b) (hμ : μ a < μ b) :
    height N μ < height N (μ ∘ Equiv.swap a b) := by
  classical
  unfold height
  have hne : a ≠ b := hab.ne
  rw [← Finset.sum_add_sum_compl {a, b}, ← Finset.sum_add_sum_compl {a, b}
    (fun c => (N - c.val) * (μ ∘ Equiv.swap a b) c)]
  have hrest : ∑ c ∈ ({a, b} : Finset (Fin N))ᶜ, (N - c.val) * (μ ∘ Equiv.swap a b) c =
      ∑ c ∈ ({a, b} : Finset (Fin N))ᶜ, (N - c.val) * μ c := by
    refine Finset.sum_congr rfl fun c hc => ?_
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    simp [Equiv.swap_apply_of_ne_of_ne hc.1 hc.2]
  rw [hrest, Finset.sum_pair hne, Finset.sum_pair hne]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  apply Nat.add_lt_add_right
  have hlt : N - b.val < N - a.val := by have := b.isLt; have : a.val < b.val := hab; omega
  generalize N - b.val = q at *
  generalize N - a.val = p at *
  nlinarith

theorem isWeightedHomogeneous_rename_rows {k : Type} [Field k] {N : ℕ} (σ : Equiv.Perm (Fin N))
    {v : MvPolynomial (Fin N × Fin N) k} {μ : Fin N → ℕ}
    (hv : IsWeightedHomogeneous (rowW N N) v μ) :
    IsWeightedHomogeneous (rowW N N) (rename (fun x : Fin N × Fin N => (σ x.1, x.2)) v) (μ ∘ σ.symm) := by
  classical
  have hinj : Function.Injective (fun x : Fin N × Fin N => (σ x.1, x.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (σ.injective h.1) h.2
  intro d hd
  have hmem : d ∈ (rename (fun x : Fin N × Fin N => (σ x.1, x.2)) v).support := mem_support_iff.mpr hd
  rw [support_rename_of_injective hinj, Finset.mem_image] at hmem
  obtain ⟨u, hu, rfl⟩ := hmem
  have hw := hv (mem_support_iff.mp hu)
  funext a
  rw [weight_rowW_apply, Function.comp_apply, ← hw, weight_rowW_apply]
  unfold rowDeg
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show ((a, s) : Fin N × Fin N) = (fun x : Fin N × Fin N => (σ x.1, x.2)) (σ.symm a, s) by simp]
  exact Finsupp.mapDomain_apply_of_injective hinj u _

end GlobalTheory.Alc.HighestVec


open GlobalTheory.Alc.HighestVec in
theorem GlobalTheory.Alc.exists_dominant_highest_vector_of_lt : ∀ (k : Type) [Field k] (N : ℕ)
    (M M' : Submodule k (MvPolynomial (Fin N × Fin N) k)), Good M → Good M' → M < M' →
    (∃ c : ℕ, ∀ f ∈ M', ∀ m ∈ f.support, ∑ a, rowDeg m a ≤ c) →
    ∃ (μ : Fin N → ℕ) (v : MvPolynomial (Fin N × Fin N) k), Antitone μ ∧ v ∈ M' ∧ v ∉ M ∧
      IsWeightedHomogeneous (rowW N N) v μ ∧ ∀ a b, a < b → rowE k N N a b v ∈ M := by
  open GlobalTheory.Alc.HighestVec in
  intro k _ N M M' hM hM' hlt hc
  obtain ⟨c, hc⟩ := hc
  classical
  let S : Set ℕ := {h | ∃ (μ : Fin N → ℕ) (v : MvPolynomial (Fin N × Fin N) k), v ∈ M' ∧ v ∉ M ∧
    IsWeightedHomogeneous (rowW N N) v μ ∧ height N μ = h}
  have hne : S.Nonempty := by
    obtain ⟨f, hfM', hfM⟩ := SetLike.exists_of_lt hlt
    by_contra hcon
    apply hfM
    rw [← sum_weightedHomogeneousComponent (rowW N N) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    refine Submodule.sum_mem _ fun μ _ => ?_
    by_contra hμ
    exact hcon ⟨_, μ, _, hM'.2.1 μ f hfM', hμ,
      weightedHomogeneousComponent_isWeightedHomogeneous μ f, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨N * c, ?_⟩
    rintro h ⟨μ, v, hv', hvM, hvh, rfl⟩
    have hv0 : v ≠ 0 := fun h0 => hvM (h0 ▸ M.zero_mem)
    obtain ⟨m, hm⟩ := ne_zero_iff.mp hv0
    have hw := hvh hm
    have hsum := hc v hv' m (mem_support_iff.mpr hm)
    have hμm : ∀ a, μ a = rowDeg m a := fun a => by rw [← hw, weight_rowW_apply]
    calc height N μ = ∑ a, (N - a.val) * μ a := rfl
      _ ≤ ∑ a, N * μ a := Finset.sum_le_sum fun a _ => Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = N * ∑ a, rowDeg m a := by rw [Finset.mul_sum]; simp only [hμm]
      _ ≤ N * c := Nat.mul_le_mul_left _ hsum
  obtain ⟨μ, v, hv', hvM, hvh, hH⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ (μ' : Fin N → ℕ) (v' : MvPolynomial (Fin N × Fin N) k), v' ∈ M' → v' ∉ M →
      IsWeightedHomogeneous (rowW N N) v' μ' → height N μ' ≤ height N μ := by
    intro μ' v' h1 h2 h3
    rw [hH]
    exact le_csSup hbdd ⟨μ', v', h1, h2, h3, rfl⟩
  refine ⟨μ, v, ?_, hv', hvM, hvh, ?_⟩
  · intro a b hab
    rcases hab.lt_or_eq with hab | rfl
    · by_contra hba
      push_neg at hba
      have h1 : rename (fun x : Fin N × Fin N => (Equiv.swap a b x.1, x.2)) v ∈ M' :=
        hM'.2.2 (Equiv.swap a b) v hv'
      have h2 : rename (fun x : Fin N × Fin N => (Equiv.swap a b x.1, x.2)) v ∉ M := by
        intro h
        apply hvM
        have h' := hM.2.2 (Equiv.swap a b) _ h
        rw [rename_rename] at h'
        have hid : ((fun x : Fin N × Fin N => (Equiv.swap a b x.1, x.2)) ∘
            fun x : Fin N × Fin N => (Equiv.swap a b x.1, x.2)) = id := by
          funext x; simp
        rwa [hid, rename_id_apply] at h'
      have h3 := isWeightedHomogeneous_rename_rows (Equiv.swap a b) hvh
      rw [Equiv.symm_swap] at h3
      have h4 := hmax _ _ h1 h2 h3
      have h5 := height_lt_swap N μ a b hab hba
      omega
    · exact le_rfl
  · intro a b hab
    by_contra hnot
    have hne : a ≠ b := hab.ne
    obtain ⟨_, hE⟩ := GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight k N N μ v hvh
    obtain ⟨hz, hw⟩ := hE a b hne
    by_cases hb : μ b = 0
    · exact hnot (by rw [hz hb]; exact M.zero_mem)
    · let μ' : Fin N → ℕ := μ + Pi.single a 1 - Pi.single b 1
      have hμ' : μ' + Pi.single b 1 = μ + Pi.single a 1 := by
        funext c
        by_cases hca : c = a
        · subst hca; simp [μ', Pi.single_apply, hne]
        · by_cases hcb : c = b
          · subst hcb; simp [μ', Pi.single_apply, hca]; omega
          · simp [μ', Pi.single_apply, hca, hcb]
      have h3 := hw μ' hμ'
      have h1 : rowE k N N a b v ∈ M' := hM'.1 a b v hv'
      have hle := hmax μ' _ h1 hnot h3
      have hh := congrArg (height N) hμ'
      rw [height_add, height_add, height_single, height_single] at hh
      have : N - b.val < N - a.val := by
        have := b.isLt; have : a.val < b.val := hab; omega
      omega
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem eq_of_hcVal_eq : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (ν μ : Fin N → ℕ), Antitone ν → Antitone μ → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → (∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j) → μ = ν := by
  intro p hp k _ _ N ν μ hν hμ hb hval
  have hS : PowerSeries.mk (hcVal k fun i => (μ i : k)) = PowerSeries.mk (hcVal k fun i => (ν i : k)) := by
    ext j
    simp [hval j]
  have gμ := GlobalTheory.T.traceEPowerHighestWeightValue_generating_series k N (fun i => (μ i : k))
  have gν := GlobalTheory.T.traceEPowerHighestWeightValue_generating_series k N (fun i => (ν i : k))
  rw [hS] at gμ
  have cast : ∀ (w : Fin N → ℕ) (i : Fin N),
      shift k (fun i => (w i : k)) i = ((w i + (N - 1 - i.val) : ℕ) : k) := by
    intro w i
    simp [shift]
  simp only [cast] at gμ gν
  refine GlobalTheory.T.eq_of_dominantWeights_lowestAlcove_linked p N hp ν μ hν hμ hb ?_
  refine GlobalTheory.T.residue_multiset_eq_of_shifted_series_eq p hp k N (fun i => ν i + (N - 1 - i.val)) (fun i => μ i + (N - 1 - i.val)) ?_
  rw [← gν, ← gμ]
  ring

end GlobalTheory.Alc
end

section

open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.JacobiTriple

theorem tripleProduct : GlobalTheory.ThetaWeberRoad.TripleProduct := by
  intro τ z
  set s := cexp (π * I * (τ : ℂ)) with hs
  set x := cexp (2 * π * I * z) with hx
  have hτ : 0 < (τ : ℂ).im := τ.2
  have hs1 : ‖s‖ < 1 := norm_exp_pi_I_lt_one (τ : ℂ) hτ
  have hs0 : s ≠ 0 := exp_ne_zero _
  have hx0 : x ≠ 0 := exp_ne_zero _
  have ht1 : ‖s ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg s]
  obtain ⟨hP, hP0, -⟩ := qPoch_tendsto (s ^ 2) ht1
  have hT := GlobalTheory.T.jacobi_triple_product_limit (τ : ℂ) z hτ
  rw [(multipliable_tpFactor τ z).hasProd_iff_tendsto_nat]
  have key : ∀ n : ℕ, ∏ k ∈ Finset.range n, GlobalTheory.ThetaWeberRoad.tpFactor τ z k =
      qPoch (s ^ 2) n * ∑ j ∈ Finset.Icc (-(n : ℤ)) n,
        finCoeff (cexp (π * I * (τ : ℂ)) ^ 2) n j * jacobiTheta₂_term j z τ := by
    intro n
    rw [Finset.prod_congr rfl (fun k _ => tpFactor_eq τ z k), Finset.prod_mul_distrib]
    have hf := GlobalTheory.T.jacobiTriple_finite_product s x hs0 hs1 hx0 n
    simp only [hs, hx] at hf
    simp only [hf, jacobiTheta₂_term_eq_zpow]
    rfl
  simp_rw [key]
  have := hP.mul hT
  rwa [mul_left_comm, mul_inv_cancel₀ hP0, mul_one] at this

end GlobalTheory.JacobiTriple
end
end
