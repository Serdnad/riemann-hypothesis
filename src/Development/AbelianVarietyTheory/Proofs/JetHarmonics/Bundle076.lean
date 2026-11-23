module

public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
public import Formalism.LocalToGlobal.CharacterGerms.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle006
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle025
public import Formalism.PeriodIntegrals.Bundle004
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Formalism.RealPlaceAnalysis.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle048
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle065
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle053
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusWeightEigenAndRootShift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.Ultra
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle020
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.Bundle001

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FlagFix

open Formalism.QuantumDeterminants

theorem wedge_eq_of_mul {n l : ℕ} (f f' : Fin l → Fin n → ℂ) (U : Matrix (Fin l) (Fin l) ℂ)
    (hU0 : ∀ c a, a < c → U c a = 0) (hU1 : ∀ c, U c c = 1)
    (h : ∀ i a, f' a i = ∑ c, f c i * U c a) : wedge f' = wedge f := by
  have dU : U.det = 1 := by
    have ht : U.IsUpperTriangular := fun i j hij => hU0 i j hij
    rw [det_of_isUpperTriangular ht]
    exact Finset.prod_eq_one (fun i _ => hU1 i)
  funext I
  have e : (Matrix.of fun a b : Fin l => f' b (I.1.orderEmbOfFin I.2 a)) =
      (Matrix.of fun a b : Fin l => f b (I.1.orderEmbOfFin I.2 a)) * U := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, h]
  simp only [wedge]
  rw [e, det_mul, dU, mul_one]

theorem flat_eq (k r : ℕ) (f : Fin (2 * r + k + 1) → ℂ) : flat k r f = star f ᵥ* Hpk k r := by
  funext c
  simp only [flat, herm]
  rw [dotProduct_mulVec, dotProduct_single, mul_one]

theorem dual_fix (k r : ℕ) (f : Fin (2 * r + k + 1) → ℂ)
    (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hs : sᴴ * Hpk k r * s = Hpk k r)
    (hf : s *ᵥ f = f) : dualM s *ᵥ flat k r f = flat k r f := by
  have h2 : Hpk k r * Hpk k r = 1 := (hermitian_pos_facts_hold k r).2.1
  have hl : (Hpk k r * sᴴ * Hpk k r) * s = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc sᴴ, hs, h2]
  rw [flat_eq, dualM, mulVec_transpose, Matrix.inv_eq_left_inv hl, vecMul_vecMul,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, ← vecMul_vecMul, ← star_mulVec, hf]

theorem fixes_wedge_and_form : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z,
      cmp (r + 1) s *ᵥ (wedge (Formalism.QuantumDeterminants.fvec k r z)) = (wedge (Formalism.QuantumDeterminants.fvec k r z)) ∧
      dualM s *ᵥ (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) = (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) := by
  intro k r z hz s hs
  obtain ⟨U, hU0, hU1, hF⟩ := S_F hz hs
  have key : ∀ i a, (s *ᵥ fvec k r z a) i = ∑ c, fvec k r z c i * U c a := by
    intro i a
    have := congrFun (congrFun hF i) a
    simpa [Matrix.mul_apply, Fm, mulVec, dotProduct] using this
  refine ⟨?_, dual_fix k r _ s (Sset_UH hs) ?_⟩
  · rw [(GlobalTheory.T.compoundMatrix_cauchyBinet_properties _ (r + 1) s s).2.2.2]
    exact wedge_eq_of_mul _ _ U hU0 hU1 key
  · funext i
    rw [key, Finset.sum_eq_single 0, hU1, mul_one]
    · intro c _ hc
      rw [hU0 c 0 (Fin.pos_of_ne_zero hc), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.FlagFix
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RowBudgets

lemma level_le (k l : ℕ) (hk : 1 ≤ k) (hl : 5 ≤ l) :
    ((RF.i0 k l : ℕ) : ℝ) ≤ 3 + 2 * Real.log k := by
  have h := GlobalTheory.LevelsOrbits.levelBound k l hk hl
  have e : RF.i0 k l = Formalism.L2.FormalSeriesBounds.i0 k l := rfl
  rw [e]
  linarith

theorem main : ∀ (r f n m nW T l k : ℕ) (b L A : ℝ), 1 ≤ m → m ≤ n → n ≤ r → 2 ≤ f → 1 ≤ T → n + 1 = k → 3 ≤ L → Real.log k ≤ L → 10 * (r : ℝ) * (f + (f : ℝ) ^ 2 * (n : ℝ) ^ 3 * L ^ 2 / m) ≤ nW →
  8 * r * f ≤ nW ∧ (5 ≤ l → f * (RF.i0 k l * n) + 2 * r * f ≤ nW) ∧
  (3 ≤ l → 0 ≤ b → m * b / (T * f * (n : ℝ) ^ 3 * L) ≤ l → ∃ s : ℕ, 4 * r * s * f ≤ nW ∧ ∀ x : ℕ, (T : ℝ) * x ≤ 3 * b → x ≤ s * (l - 1)) ∧
  (0 < l → (l : ℝ) < m * b / (T * f * (n : ℝ) ^ 3 * L) → b ≤ A → T * f * (n : ℝ) ^ 3 * Real.log k ^ 2 ≤ Real.log k * m * A / l) := by
  intro r f n m nW T l k b L A hm hmn hnr hf hT hk hL hkL hW
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hnr' : (n : ℝ) ≤ r := by exact_mod_cast hnr
  have hf' : (2 : ℝ) ≤ f := by exact_mod_cast hf
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hk1 : 1 ≤ k := by omega
  have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
  have hn' : (1 : ℝ) ≤ n := hm'.trans hmn'
  have hr' : (1 : ℝ) ≤ r := hn'.trans hnr'
  have hD : (0 : ℝ) < T * f * (n : ℝ) ^ 3 * L := by positivity
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = f * (n : ℝ) ^ 3 * L / m := ⟨_, rfl⟩
  have hYm : Y * m = f * (n : ℝ) ^ 3 * L := by rw [hY]; field_simp
  have hW' : 10 * ((r : ℝ) * f) + 10 * L * (r * f * Y) ≤ nW := by
    refine le_of_eq_of_le ?_ hW
    rw [hY]; ring
  have hYL : L ≤ Y := by
    rw [hY, le_div_iff₀ (by positivity)]
    have h1 : (m : ℝ) ≤ (n : ℝ) ^ 3 := hmn'.trans (le_self_pow₀ hn' (by norm_num))
    have h2 : (n : ℝ) ^ 3 ≤ f * (n : ℝ) ^ 3 := le_mul_of_one_le_left (by positivity) (by linarith)
    have h3 := mul_le_mul_of_nonneg_right (h1.trans h2) (show 0 ≤ L by linarith)
    linarith
  have hrf : (0 : ℝ) ≤ r * f := by positivity
  have hP : (0 : ℝ) ≤ r * f * Y := mul_nonneg hrf (by linarith)
  have hPL : 3 * (r * f * Y) ≤ L * (r * f * Y) := mul_le_mul_of_nonneg_right hL hP
  refine ⟨?_, fun hl => ?_, fun hl hb h => ?_, fun hl h hA => ?_⟩
  · have : (8 * r * f : ℝ) ≤ nW := by linarith
    exact_mod_cast this
  · have h1 : ((RF.i0 k l : ℕ) : ℝ) ≤ 3 * Y := by
      have := level_le k l hk1 hl
      linarith
    have h2 : ((RF.i0 k l : ℕ) : ℝ) * n ≤ 3 * Y * r :=
      mul_le_mul h1 hnr' (by positivity) (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ f by positivity)
    have : (f * (((RF.i0 k l : ℕ) : ℝ) * n) + 2 * r * f : ℝ) ≤ nW := by linarith
    exact_mod_cast this
  · have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
    have hq : (0 : ℝ) < T * ((l : ℝ) - 1) := mul_pos (by linarith) (by linarith)
    rw [div_le_iff₀ hD] at h
    have hbY : b ≤ l * T * Y := by
      refine le_of_mul_le_mul_left (a := (m : ℝ)) ?_ (by linarith)
      calc (m : ℝ) * b ≤ l * (T * f * (n : ℝ) ^ 3 * L) := h
        _ = l * T * (Y * m) := by rw [hYm]; ring
        _ = _ := by ring
    have hTY : (0 : ℝ) ≤ T * Y := mul_nonneg (by linarith) (by linarith)
    have hz : 3 * b / (T * ((l : ℝ) - 1)) ≤ 6 * Y := by
      rw [div_le_iff₀ hq]
      have := mul_le_mul_of_nonneg_right hl' hTY
      nlinarith
    refine ⟨⌈3 * b / (T * ((l : ℝ) - 1))⌉₊, ?_, fun x hx => ?_⟩
    · have h1 := (Nat.ceil_lt_add_one (show 0 ≤ 3 * b / (T * ((l : ℝ) - 1)) by positivity)).le
      have h2 := mul_le_mul_of_nonneg_left (h1.trans (add_le_add_left hz 1)) hrf
      have : (4 * r * (⌈3 * b / (T * ((l : ℝ) - 1))⌉₊ : ℝ) * f : ℝ) ≤ nW := by linarith
      exact_mod_cast this
    · have h1 := Nat.le_ceil (3 * b / (T * ((l : ℝ) - 1)))
      rw [div_le_iff₀ hq] at h1
      have h2 : (x : ℝ) ≤ (⌈3 * b / (T * ((l : ℝ) - 1))⌉₊ : ℝ) * ((l : ℝ) - 1) := by
        refine le_of_mul_le_mul_left (a := (T : ℝ)) ?_ (by linarith)
        linarith
      have h3 : ((l : ℝ) - 1) = ((l - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]; simp
      generalize ⌈3 * b / (T * ((l : ℝ) - 1))⌉₊ = s at h2 ⊢
      rw [h3] at h2
      exact_mod_cast h2
  · have hl' : (0 : ℝ) < l := by exact_mod_cast hl
    rw [lt_div_iff₀ hD] at h
    rw [le_div_iff₀ hl']
    have h1 : (m : ℝ) * b ≤ m * A := mul_le_mul_of_nonneg_left hA (by linarith)
    have h2 : l * (T * f * (n : ℝ) ^ 3 * Real.log k) ≤ l * (T * f * (n : ℝ) ^ 3 * L) := by
      gcongr
    have h3 := mul_le_mul_of_nonneg_left (h2.trans (h.le.trans h1)) hlog
    linarith

end GlobalTheory.RowBudgets
end

section

namespace GlobalTheory.ClosedValuedField

open scoped NNReal

theorem exists_isAlgClosed_forall_isAdicComplete (F₀ : Type) [Field F₀] [IsAlgClosed F₀]
    (v₀ : AddValuation F₀ (WithTop ℚ)) {a : F₀} (ha : a ≠ 0) (hv : 0 < v₀ a) :
    ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (e : F₀ →+* F)
      (v : AddValuation F (WithTop ℚ)), (∀ x, v (e x) = v₀ x) ∧
      ∀ b : ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v, 0 < v (b : F) →
        IsAdicComplete (Ideal.span {b}) (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) := by
  let w := expNegAbsoluteValue v₀
  have hw : ∀ x, w x = (expNegTop (v₀ x) : ℝ) := fun _ => rfl
  have hp1 : w a < 1 := by
    rw [hw, ← NNReal.coe_one, NNReal.coe_lt_coe, ← expNegTop_zero, ← not_le, expNegTop_le_iff]
    exact not_le.2 hv
  have hp0 : 0 < w a := w.pos ha
  letI : NontriviallyNormedField (WithAbs w) :=
    { (inferInstance : NormedField (WithAbs w)) with
      non_trivial := ⟨(WithAbs.toAbs w a)⁻¹, by
        rw [norm_inv]
        change 1 < (w a)⁻¹
        exact (one_lt_inv₀ hp0).2 hp1⟩ }
  haveI : IsUltrametricDist (WithAbs w) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y =>
      isNonarchimedean_expNegAbsoluteValue v₀ x.ofAbs y.ofAbs
  haveI : IsAlgClosed (WithAbs w) := IsAlgClosed.of_ringEquiv F₀ _ (WithAbs.equiv w).symm
  let C := UniformSpace.Completion (WithAbs w)
  letI : NontriviallyNormedField C := completionNontriviallyNormedField (WithAbs w)
  haveI : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra (WithAbs w)
  haveI : IsAlgClosed C :=
    isAlgClosed_of_denseRange (K := WithAbs w) UniformSpace.Completion.denseRange_coe
  let e : F₀ →+* C := (algebraMap (WithAbs w) C).comp (WithAbs.equiv w).symm.toRingHom
  have he : ∀ x, ‖e x‖₊ = expNegTop (v₀ x) := fun x =>
    NNReal.coe_injective (UniformSpace.Completion.norm_coe (WithAbs.toAbs w x))
  obtain ⟨v, hvC⟩ := exists_addValuation_expNegTop_eq_nnnorm (C := C) fun x => by
    obtain ⟨y, hy⟩ := exists_norm_eq_of_completion x
    exact ⟨v₀ y.ofAbs, NNReal.coe_injective hy.symm⟩
  have hmem : ∀ x : C, NormedField.valuation x ≤ 1 ↔ 0 ≤ v x := fun x => by
    rw [NormedField.valuation_apply, ← hvC, ← expNegTop_zero, expNegTop_le_iff]
  have hO : (NormedField.valuation (K := C)).Integers (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) :=
    ⟨Subtype.val_injective, fun x => (hmem _).2 x.2, fun r hr => ⟨⟨r, (hmem r).1 hr⟩, rfl⟩⟩
  refine ⟨C, inferInstance, inferInstance, e, v,
    fun x => expNegTop_inj_of_eq (by rw [hvC, he]), fun b hb =>
    NormIntegers.isAdicComplete_span_singleton hO (by
      change ‖(b : C)‖ < 1
      rw [← coe_nnnorm, ← hvC, ← NNReal.coe_one, NNReal.coe_lt_coe, ← expNegTop_zero, ← not_le,
        expNegTop_le_iff]
      exact not_le.2 hb)⟩

end GlobalTheory.ClosedValuedField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.ClosedValuedField

theorem exists_field_over_cdvr : ∀ (T : CDVR) (ϖ : T.V), Irreducible ϖ → CharZero T.Fr → ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : CharZero F) (_ : Algebra T.Fr F) (_ : Algebra T.V F) (_ : IsScalarTower T.V T.Fr F) (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v ∧ ∃ (O : Type) (_ : CommRing O) (_ : Algebra O F) (_ : Algebra T.V O) (_ : IsScalarTower T.V O F), Function.Injective (algebraMap O F) ∧ (∀ z : F, 0 ≤ v z ↔ z ∈ (algebraMap O F).range) ∧ ∀ g : ℕ, g ≠ 0 → ¬ IsUnit ((g : ℕ) : T.V) → IsAdicComplete (Ideal.span {((g : ℕ) : O)}) O := by
  intro T ϖ hϖ _
  obtain ⟨v₀, hv₀⟩ := exists_valOver_of_isAlgebraic hϖ (AlgebraicClosure T.Fr)
  have hinj : Function.Injective (TWO.algVF (V := T.V) (F := AlgebraicClosure T.Fr)) :=
    (algebraMap T.Fr (AlgebraicClosure T.Fr)).injective.comp (IsFractionRing.injective T.V T.Fr)
  obtain ⟨F, _, _, e, v, he, hc⟩ := exists_isAlgClosed_forall_isAdicComplete
    (AlgebraicClosure T.Fr) v₀ ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero)
    (lt_of_lt_of_le zero_lt_one ((TWO.v_of_V v₀ hϖ hv₀ ϖ).2 hϖ.not_isUnit hϖ.ne_zero))
  letI : Algebra T.Fr F := (e.comp (algebraMap T.Fr (AlgebraicClosure T.Fr))).toAlgebra
  haveI : CharZero F := charZero_of_injective_ringHom (algebraMap T.Fr F).injective
  letI : Algebra T.V F := (TWO.algVF (V := T.V) (F := F)).toAlgebra
  haveI : IsScalarTower T.V T.Fr F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hv : ValOver ϖ F v := fun c n h => (he _).trans (hv₀ c n h)
  letI : Algebra T.V (TWO.Ov v) := (TWO.fO v hϖ hv).toAlgebra
  haveI : IsScalarTower T.V (TWO.Ov v) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, v, hv, TWO.Ov v, inferInstance, inferInstance, inferInstance, inferInstance,
    Subtype.val_injective, fun z => ⟨fun h => ⟨⟨z, h⟩, rfl⟩, ?_⟩, fun g hg hu => hc _ ?_⟩
  · rintro ⟨y, rfl⟩
    exact y.2
  · have h := (TWO.v_of_V v hϖ hv (g : T.V)).2 hu (Nat.cast_ne_zero.2 hg)
    rw [map_natCast] at h
    have e' : (((g : ℕ) : TWO.Ov v) : F) = (g : F) := map_natCast (algebraMap (TWO.Ov v) F) g
    rw [e']
    exact lt_of_lt_of_le zero_lt_one h

end GlobalTheory.ClosedValuedField
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.QuotWeil

theorem measurable_mulM {m : ℕ} {α : Type} [MeasurableSpace α] {a b : α → PI.MtM m}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun t => (fun i j => (Matrix.of (a t) * Matrix.of (b t)) i j : PI.MtM m)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
  · exact (measurable_pi_apply k).comp ((measurable_pi_apply i).comp ha)
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp hb)

theorem measurable_invM {m : ℕ} :
    Measurable (fun s : PI.MtM m => (fun i j => (Matrix.of s)⁻¹ i j : PI.MtM m)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have hc : Continuous (fun s : PI.MtM m => (Matrix.of s : Matrix (Fin m) (Fin m) ℂ)) := continuous_id
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  refine Measurable.mul (Measurable.inv hc.matrix_det.measurable) ?_
  exact (hc.matrix_adjugate.matrix_elem i j).measurable

theorem unfold_abstract {X : Type} [MeasurableSpace X] (mu : X → X → X) (iv : X → X)
    (hmu : Measurable (fun p : X × X => mu p.1 p.2)) (hiv : Measurable iv)
    (μG μS : Measure X) [SFinite μG] [SFinite μS]
    (hleft : ∀ᵐ s ∂μS, μG.map (mu s) = μG ∧ ∀ x, mu (iv s) (mu s x) = x)
    (hinv : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ s, f (iv s) ∂μS = ∫⁻ s, f s ∂μS)
    (φ : X → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∀ᵐ x ∂μG, ∫⁻ s, φ (mu s x) ∂μS = 1)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (mu s x) ∂μS) ∂(μG.withDensity φ) := by
  have hl : ∀ s, Measurable (mu s) := fun s => hmu.comp (measurable_const.prodMk measurable_id)
  have hr : ∀ x, Measurable (fun s => mu s x) := fun x =>
    hmu.comp (measurable_id.prodMk measurable_const)
  have h1 : Measurable (fun p : X × X => f (mu p.2 p.1)) := hf.comp (hmu.comp measurable_swap)
  have h2 : Measurable (fun p : X × X => φ (mu (iv p.1) p.2) * f p.2) :=
    (hφ.comp (hmu.comp ((hiv.comp measurable_fst).prodMk measurable_snd))).mul
      (hf.comp measurable_snd)
  have hF : Measurable (fun x : X => ∫⁻ s, f (mu s x) ∂μS) := h1.lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hφ hF]
  symm
  calc ∫⁻ x, (φ * fun x : X => ∫⁻ s, f (mu s x) ∂μS) x ∂μG
      = ∫⁻ x, ∫⁻ s, φ x * f (mu s x) ∂μS ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply, lintegral_const_mul]
        exact hf.comp (hr x)
    _ = ∫⁻ s, ∫⁻ x, φ x * f (mu s x) ∂μG ∂μS :=
        lintegral_lintegral_swap ((hφ.comp measurable_fst).mul h1).aemeasurable
    _ = ∫⁻ s, ∫⁻ y, φ (mu (iv s) y) * f y ∂μG ∂μS := by
        refine lintegral_congr_ae (hleft.mono fun s hs => ?_)
        have hm : Measurable (fun y : X => φ (mu (iv s) y) * f y) :=
          (hφ.comp (hl _)).mul hf
        beta_reduce
        conv_rhs => rw [← hs.1, lintegral_map hm (hl s)]
        refine lintegral_congr fun x => ?_
        rw [hs.2]
    _ = ∫⁻ y, ∫⁻ s, φ (mu (iv s) y) * f y ∂μS ∂μG := lintegral_lintegral_swap h2.aemeasurable
    _ = ∫⁻ y, f y ∂μG := by
        refine lintegral_congr_ae (hφ1.mono fun y hy => ?_)
        have hm : Measurable (fun s : X => φ (mu s y)) := hφ.comp (hr y)
        have hm' : Measurable (fun s : X => φ (mu (iv s) y)) := hm.comp hiv
        have := hinv _ hm
        beta_reduce at this ⊢
        rw [lintegral_mul_const _ hm', this, hy, one_mul]

theorem exists_isQuotM : ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS : Measure (PI.MtM m)),
    PI.IsMatGroup G → PI.IsMatGroup S → S ⊆ G → PI.IsHaarOnM G μG → PI.IsHaarOnM S μS →
    PI.IsRightInvM S μS → ∃ ν, PI.IsQuotM μG μS ν := by
  intro m G S μG μS hG hS hSG hμG hμS hR
  obtain ⟨φ, hφ, hφ1⟩ := GlobalTheory.T.exists_normalised_cutoff' m G S μS hG hS hSG hμS hR
  have hinv := GlobalTheory.T.lintegral_inv_eq_of_biInvariant_matGroup m S μS hS hμS hR
  haveI := hμG.1
  haveI := hμS.1
  have haeS : ∀ᵐ s ∂μS, Matrix.of s ∈ S := by rw [ae_iff]; exact hμS.2.2.1
  have haeG : ∀ᵐ s ∂μG, Matrix.of s ∈ G := by rw [ae_iff]; exact hμG.2.2.1
  refine ⟨μG.withDensity φ, fun f hf => ?_⟩
  refine unfold_abstract (fun s x : PI.MtM m => fun i j => (Matrix.of s * Matrix.of x) i j)
    (fun s i j => (Matrix.of s)⁻¹ i j) (measurable_mulM measurable_fst measurable_snd)
    measurable_invM μG μS (haeS.mono fun s hs => ⟨hμG.2.2.2 _ (hSG hs), fun x => ?_⟩) hinv φ hφ
    (haeG.mono fun x hx => hφ1 x hx) f hf
  have hs1 : (Matrix.of s)⁻¹ * Matrix.of s = 1 := mul_eq_one_comm.1 (hS.2.2.2 _ hs).2
  change (Matrix.of s)⁻¹ * (Matrix.of s * Matrix.of x) = Matrix.of x
  rw [← Matrix.mul_assoc, hs1, Matrix.one_mul]

end GlobalTheory.QuotWeil
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowestVector


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.LowestVector.exists_lowest_vector : _root_.PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : _root_.BranchingSupport.Rep k r), R.IsDS ε mu → ∀ (Q : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), _root_.PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∃ w : R.smSub, ‖w‖ = 1 ∧ R.KFin (w : R.H) ∧ _root_.Formalism.REAL.KHighest ε E (_root_.Formalism.QuantumDeterminants.lowK ε mu) w ∧ FiniteDimensional ℂ (_root_.Formalism.REAL.kSpan ε E w) := by
  intro hKS k r ε mu R hDS Q E hQ hE
  have hFV := (_root_.GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R hDS Q hQ
  unfold _root_.PI.UpqRep.IsDS at hFV
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hFV
  unfold _root_.PI.UpqRep.IsKTypeOf at hS
  obtain ⟨hSfd, hSK, -, ⟨v, hvS, hv0, hvw⟩, hhigh⟩ := hS
  have hlow : _root_.PI.UpqRep.lowK ε mu = _root_.Formalism.QuantumDeterminants.lowK ε mu := rfl
  have hstab := _root_.GlobalTheory.CompactStable.kStable_smooth_and_stable hKS k r ε mu R hDS Q hQ S hSfd hSK
  unfold _root_.BranchingSupport.Rep.IsE at hE
  set w0 : R.H := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hw0def
  have hw0S : w0 ∈ S := S.smul_mem _ hvS
  have hw0wt : _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) (fun g ↦ R.σ (Q⁻¹ * g * Q)) (_root_.PI.UpqRep.lowK ε mu) w0 := by
    unfold _root_.PI.UpqRep.IsWtOn at hvw ⊢
    intro θ hθ
    rw [hw0def, ContinuousLinearMap.map_smul, hvw θ hθ, smul_comm]
  have hnorm : ‖w0‖ = 1 := by
    rw [hw0def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  let w : R.smSub := ⟨w0, (hstab.1 w0 hw0S).2⟩
  have htor := _root_.GlobalTheory.TorusWeight.torus_weight_action hKS k r ε mu R hDS Q E hQ hE (_root_.PI.UpqRep.lowK ε mu) w hw0wt
  let T : Submodule ℂ R.smSub := S.comap R.smSub.subtype
  have hT : _root_.Formalism.REAL.KStable ε E T := by
    unfold _root_.Formalism.REAL.KStable
    intro a b hab x hx
    show ((E a b x : R.smSub) : R.H) ∈ S
    rw [hE]
    exact hstab.2 a b hab x hx
  have hTfd : FiniteDimensional ℂ T := by
    let f : T →ₗ[ℂ] S :=
      LinearMap.codRestrict S (R.smSub.subtype.comp T.subtype) (fun x => x.2)
    refine Module.Finite.of_injective f ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hval := congrArg Subtype.val hxy
    exact hval
  have hle : _root_.Formalism.REAL.kSpan ε E w ≤ T := by
    unfold _root_.Formalism.REAL.kSpan
    exact sInf_le ⟨hw0S, hT⟩
  refine ⟨w, hnorm, (hstab.1 w0 hw0S).1, ?_, Submodule.finiteDimensional_of_le hle⟩
  unfold _root_.Formalism.REAL.KHighest
  refine ⟨htor.1, ?_⟩
  intro a b hab hεab
  by_contra hne
  have hmem : ((E a b w : R.smSub) : R.H) ∈ S := by
    rw [hE]
    exact hstab.2 a b hεab w0 hw0S
  have hne' : ((E a b w : R.smSub) : R.H) ≠ 0 := fun h => hne (Submodule.coe_eq_zero.mp h)
  exact _root_.GlobalTheory.DominantRootSums.not_cDom_add_root _ ε (_root_.PI.UpqRep.lowK ε mu) a b hab
    (hhigh _ _ hmem hne' (htor.2 a b))

end GlobalTheory.LowestVector
end
end
