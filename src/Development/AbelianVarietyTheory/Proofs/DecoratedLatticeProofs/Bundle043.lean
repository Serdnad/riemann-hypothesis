module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardFilterLowerHeckeRepsEqRelIndexPow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle036
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.DegreeLeOfMemAntidiagonal
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardFilterParahoricCosetsEqSchurCount
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle040
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
public import Mathlib.RingTheory.PowerSeries.Expand
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

theorem _root_.GlobalTheory.T.exists_lowerUnipotent_blockDiag_coset_rep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ j ∈ parahoric k A D, ∃ g ∈ R, ∃ ν₀ : Matrix D A k, (∀ i a, valuation k (ν₀ i a) < 1) ∧ ∀ ν : Matrix D A k, (∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν₀ - ν = g.1 * μ) → (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g) * mtor ϖ (indic s))⁻¹ * (j * mtor ϖ (indic s)) ∈ parahoric k A D := by
  first | exact @GlobalTheory.LowerHecke.exists_lowU_diag_coset | exact GlobalTheory.LowerHecke.exists_lowU_diag_coset | (intros; apply GlobalTheory.LowerHecke.exists_lowU_diag_coset <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
open Classical

theorem _root_.GlobalTheory.T.card_filter_lowerHecke_reps_eq_relIndex_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (m g y : GL D k), (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') → (∃ κ'' ∈ KO k D, y = m * g * κ'') → ∀ N : Finset (Matrix D A k), ((∀ ν ∈ N, ∀ i a, valuation k (ν i a) < 1) ∧ ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) → ∃! ν', ν' ∈ N ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ) → (N.filter fun ν => ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧ (∀ i a, valuation k (ν₂ i a) < 1) ∧ m.1 * ν = ν₁ + y.1 * ν₂).card = ((preLat m.1 ⊓ preLat (g⁻¹).1).relIndex (preLat m.1 ⊓ mLat k D)) ^ Fintype.card A ∧ 0 < (preLat m.1 ⊓ preLat (g⁻¹).1).relIndex (preLat m.1 ⊓ mLat k D) := by
  first | exact @GlobalTheory.LowerHeckeCount.card_filter_eq | exact GlobalTheory.LowerHeckeCount.card_filter_eq | (intros; apply GlobalTheory.LowerHeckeCount.card_filter_eq <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda

theorem _root_.GlobalTheory.T.height_two_hondaType_first_coeff_norm_eq_one : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ c : ℕ → K, (∀ j, ‖c j‖ ≤ 1) → CoefLe ‖(l : K)‖ (C (l : K) * f - hondaSum (σ ^ 2) (l ^ 2) c f) → (∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy f e (l : K))‖ = 1) → ‖c 0‖ = 1 := by
  first | exact @GlobalTheory.Honda.HeightTwo.norm_first_coeff_eq_one | exact GlobalTheory.Honda.HeightTwo.norm_first_coeff_eq_one | (intros; apply GlobalTheory.Honda.HeightTwo.norm_first_coeff_eq_one <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.exists_parahoric_and_integralGL_doubleCosetReps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D], (∀ g : GL (A ⊕ D) k, ∃ R d, IsReps g R d) ∧ ∀ g : GL D k, ∃ R, IsRepsK g R := by
  first | exact @GlobalTheory.ParHeckeReps.exists_reps_both | exact GlobalTheory.ParHeckeReps.exists_reps_both | (intros; apply GlobalTheory.ParHeckeReps.exists_reps_both <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

theorem coefLe_mv_of_ps {K : Type} [NormedField K] {r : ℝ} {A : K⟦X⟧} (h : ∀ n, ‖coeff n A‖ ≤ r) :
    ∀ m : Unit →₀ ℕ, ‖MvPowerSeries.coeff m A‖ ≤ r := by
  intro m
  have hm : m = Finsupp.single () (m ()) := by
    ext
    simp
  rw [hm]
  exact h (m ())

theorem norm_ringHom_pow_apply {K : Type} [NormedField K] (σ : K →+* K) (hσ : ∀ x, ‖σ x‖ = ‖x‖) :
    ∀ (j : ℕ) (x : K), ‖(σ ^ j) x‖ = ‖x‖ := by
  intro j x
  induction j generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (ih (σ x)).trans (hσ x)

private theorem norm_coeff_pow_le_one {K : Type} [NormedField K] [IsUltrametricDist K] {s : Type}
    (M : MvPowerSeries s K) (hM : ∀ m, ‖MvPowerSeries.coeff m M‖ ≤ 1) :
    ∀ (N : ℕ) (m : s →₀ ℕ), ‖MvPowerSeries.coeff m (M ^ N)‖ ≤ 1 := by
  classical
  intro N
  induction N with
  | zero =>
    intro m
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  | succ N ih =>
    intro m
    rw [pow_succ, MvPowerSeries.coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ih _) (norm_nonneg _) (hM _)

theorem frobLog_eigen : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) →
    ∀ (i : ℕ), 0 < i → CoefLe ‖(l : K)‖ ((frobOp σ l i f).subst (Formalism.L2.Th1.C.mulBy f e w) -
      C ((σ ^ i) w) * frobOp σ l i f) := by
  intro K _ _ _ l σ hU f e hf w hw i hi
  have hU' := hU
  obtain ⟨hlp, -, hl1, -, hσn, -⟩ := hU
  obtain ⟨hlog, hd, hint⟩ := hf
  obtain ⟨h0, h1, h0', hfe, hef⟩ := hlog
  have hn : l ^ i ≠ 0 := pow_ne_zero _ hlp.ne_zero
  have hτ : ∀ x : K, ‖(σ ^ i) x‖ = ‖x‖ := norm_ringHom_pow_apply σ hσn i
  set g := PowerSeries.map (σ ^ i) f with hg
  set e' := PowerSeries.map (σ ^ i) e with he'
  have hXm : MvPowerSeries.map (σ ^ i) (PowerSeries.X : K⟦X⟧) = PowerSeries.X := PowerSeries.map_X _
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hg, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  have he0 : PowerSeries.constantCoeff e' = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, he', PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0', map_zero]
  have hef' : PowerSeries.subst e' g = PowerSeries.X := by
    have := congrArg (MvPowerSeries.map (σ ^ i)) hef
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h0'), hXm] at this
    exact this
  have hd' : CoefLe 1 (d⁄dX g) := by
    intro k
    rw [PowerSeries.coeff_derivative, hg, PowerSeries.coeff_map]
    have hk : (σ ^ i) ((PowerSeries.coeff (k + 1)) f) * ((k : K) + 1)
        = (σ ^ i) ((PowerSeries.coeff (k + 1)) f * ((k : K) + 1)) := by
      rw [map_mul, map_add (f := _), map_one, map_natCast]
    rw [hk, hτ, ← PowerSeries.coeff_derivative]
    exact hd k
  set M := Formalism.L2.Th1.C.mulBy f e w with hMdef
  have hCf0 : PowerSeries.constantCoeff (PowerSeries.C w * f) = 0 := by
    rw [map_mul, h0, mul_zero]
  have hM0 : MvPowerSeries.constantCoeff M = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hCf0 _ h0'
  have hMint : ∀ m, ‖MvPowerSeries.coeff m M‖ ≤ 1 := coefLe_mv_of_ps hw
  have hAB := GlobalTheory.T.pow_prime_pow_sub_frobeniusTwist_norm_le K l σ hU' Unit M hMint i hn
  set A := M ^ l ^ i with hA
  set B := MvPowerSeries.expand (l ^ i) hn (MvPowerSeries.map (σ ^ i) M) with hB
  have hA0 : MvPowerSeries.constantCoeff A = 0 := by
    rw [hA, map_pow, hM0, zero_pow hn]
  have hB0 : MvPowerSeries.constantCoeff B = 0 := by
    simp [hB, hM0]
  have hA1 : ∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1 := fun m => norm_coeff_pow_le_one M hMint _ m
  have hB1 : ∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1 := by
    intro m
    have hb : MvPowerSeries.coeff m B
        = MvPowerSeries.coeff m A + -(MvPowerSeries.coeff m (A - B)) := by
      rw [map_sub]
      ring
    rw [hb]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_neg]
    exact max_le (hA1 m) ((hAB m).trans hl1.le)
  have key := GlobalTheory.T.subst_congr_mod_prime_of_integral_derivative K l hlp hl1 g hd' Unit A B hA0 hB0 hA1 hB1 hAB
  have hsM : PowerSeries.subst M (frobOp σ l i f) = PowerSeries.subst A g := by
    have has := PowerSeries.HasSubst.of_constantCoeff_zero hM0
    unfold frobOp
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hn) has,
      PowerSeries.subst_pow has, PowerSeries.subst_X has]
  set c := (σ ^ i) w with hc
  have hq0 : PowerSeries.constantCoeff (PowerSeries.C c * g) = 0 := by
    rw [map_mul, hg0, mul_zero]
  have hmapM : MvPowerSeries.map (σ ^ i) M = PowerSeries.subst (PowerSeries.C c * g) e' := by
    have hm : MvPowerSeries.map (σ ^ i) (PowerSeries.C w * f) = PowerSeries.C c * g := by
      change PowerSeries.map (σ ^ i) (PowerSeries.C w * f) = _
      rw [map_mul, PowerSeries.map_C]
    rw [hMdef]
    unfold Formalism.L2.Th1.C.mulBy
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hCf0), hm]
  have hexp : MvPowerSeries.expand (l ^ i) hn (PowerSeries.C c * g)
      = PowerSeries.C c * PowerSeries.subst (PowerSeries.X ^ l ^ i) g := by
    change PowerSeries.expand (l ^ i) hn (PowerSeries.C c * g) = _
    rw [PowerSeries.expand_apply, PowerSeries.subst_mul (PowerSeries.HasSubst.X_pow hn),
      PowerSeries.subst_C]
    rfl
  have hexp0 : MvPowerSeries.constantCoeff (MvPowerSeries.expand (l ^ i) hn (PowerSeries.C c * g)) = 0 := by
    rw [MvPowerSeries.constantCoeff_expand]
    exact hq0
  have hBg : PowerSeries.subst B g = PowerSeries.C c * frobOp σ l i f := by
    rw [hB, hmapM, PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.of_constantCoeff_zero hq0),
      ← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' he0)
        (PowerSeries.HasSubst.of_constantCoeff_zero hexp0),
      hef', PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hexp0), hexp]
    rfl
  intro k
  rw [hsM, ← hBg]
  exact key (Finsupp.single () k)

end GlobalTheory.Honda
end

section

open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

open Formalism.L2.Th1.C

theorem twistLog_norm_iterate {K : Type} [NormedField K] (σ : K →+* K) (hσ : ∀ x : K, ‖σ x‖ = ‖x‖) (i : ℕ)
    (x : K) : ‖(σ ^ i) x‖ = ‖x‖ := by
  induction i generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (ih (σ x)).trans (hσ x)

theorem twistLog_additive_mod : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ (i : ℕ), 0 < i → ∀ m,
      ‖MvPowerSeries.coeff m (Formalism.L2.Th1.C.be0 f e (frobOp σ l i f) (MvPowerSeries.X (0 : Fin 2))
        (MvPowerSeries.X (1 : Fin 2)))‖ ≤ ‖(l : K)‖ := by
  intro K _ _ _ l σ hU f e hf i hi m
  have hU' := hU
  obtain ⟨hlp, -, hl1, -, hσn, -⟩ := hU
  obtain ⟨hlog, hd, hint⟩ := hf
  have hlog0 := hlog
  obtain ⟨h0, h1, h0', hfe, hef⟩ := hlog
  have hn : l ^ i ≠ 0 := pow_ne_zero _ hlp.ne_zero
  have hτ : ∀ x : K, ‖(σ ^ i) x‖ = ‖x‖ := twistLog_norm_iterate σ hσn i
  set g := PowerSeries.map (σ ^ i) f with hg
  set e' := PowerSeries.map (σ ^ i) e with he'
  have hXm : MvPowerSeries.map (σ ^ i) (PowerSeries.X : K⟦X⟧) = PowerSeries.X := PowerSeries.map_X _
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hg, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  have he0 : PowerSeries.constantCoeff e' = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, he', PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0', map_zero]
  have hlog' : IsLogPair g e' := by
    refine ⟨hg0, ?_, he0, ?_, ?_⟩
    · rw [hg, PowerSeries.coeff_map, h1, map_one]
    · have := congrArg (MvPowerSeries.map (σ ^ i)) hfe
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h0), hXm] at this
      exact this
    · have := congrArg (MvPowerSeries.map (σ ^ i)) hef
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h0'), hXm] at this
      exact this
  have hd' : CoefLe 1 (d⁄dX g) := by
    intro k
    rw [PowerSeries.coeff_derivative, hg, PowerSeries.coeff_map]
    have hk : (σ ^ i) ((PowerSeries.coeff (k + 1)) f) * ((k : K) + 1)
        = (σ ^ i) ((PowerSeries.coeff (k + 1)) f * ((k : K) + 1)) := by
      rw [map_mul, map_add (f := _), map_one, map_natCast]
    rw [hk, hτ, ← PowerSeries.coeff_derivative]
    exact hd k
  set X0 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0 with hX0
  set X1 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1 with hX1
  have hX00 : MvPowerSeries.constantCoeff X0 = 0 := by simp [X0]
  have hX10 : MvPowerSeries.constantCoeff X1 = 0 := by simp [X1]
  set F := fadd f e X0 X1 with hF
  have hF0 : MvPowerSeries.constantCoeff F = 0 := Pts.constantCoeff_fadd hlog0 hX00 hX10
  have hFint : ∀ m, ‖MvPowerSeries.coeff m F‖ ≤ 1 := fun m => hint m
  have hAB := GlobalTheory.T.pow_prime_pow_sub_frobeniusTwist_norm_le K l σ hU' (Fin 2) F hFint i hn
  set A := F ^ l ^ i with hA
  set B := MvPowerSeries.expand (l ^ i) hn (MvPowerSeries.map (σ ^ i) F) with hB
  have hA0 : MvPowerSeries.constantCoeff A = 0 := by
    rw [hA, map_pow, hF0, zero_pow hn]
  have hB0 : MvPowerSeries.constantCoeff B = 0 := by
    simp [hB, hF0]
  have hA1 : ∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1 := fun m => IntegralMvPolynomialLemmas.intMv_pow hint (l ^ i) m
  have hB1 : ∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1 := by
    intro m
    have hb : MvPowerSeries.coeff m B
        = MvPowerSeries.coeff m A + -(MvPowerSeries.coeff m (A - B)) := by
      rw [map_sub]
      ring
    rw [hb]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_neg]
    exact max_le (hA1 m) ((hAB m).trans hl1.le)
  have key := GlobalTheory.T.subst_congr_mod_prime_of_integral_derivative K l hlp hl1 g hd' (Fin 2) A B hA0 hB0 hA1 hB1 hAB m
  have hsX : ∀ a : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff a = 0 →
      PowerSeries.subst a (frobOp σ l i f) = PowerSeries.subst (a ^ l ^ i) g := by
    intro a ha
    have has := PowerSeries.HasSubst.of_constantCoeff_zero ha
    unfold frobOp
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hn) has,
      PowerSeries.subst_pow has, PowerSeries.subst_X has]
  have hs0 : MvPowerSeries.constantCoeff (PowerSeries.subst X0 g + PowerSeries.subst X1 g) = 0 := by
    rw [map_add (f := _), PowerSeries.constantCoeff_subst_eq_zero hX00 _ hg0,
      PowerSeries.constantCoeff_subst_eq_zero hX10 _ hg0, add_zero]
  have hs0f : MvPowerSeries.constantCoeff (PowerSeries.subst X0 f + PowerSeries.subst X1 f) = 0 := by
    rw [map_add (f := _), PowerSeries.constantCoeff_subst_eq_zero hX00 _ h0,
      PowerSeries.constantCoeff_subst_eq_zero hX10 _ h0, add_zero]
  have hmapF : MvPowerSeries.map (σ ^ i) F
      = PowerSeries.subst (PowerSeries.subst X0 g + PowerSeries.subst X1 g) e' := by
    rw [hF]
    unfold fadd
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs0f), map_add (f := _),
      PowerSeries.map_subst (PowerSeries.HasSubst.X 0), PowerSeries.map_subst (PowerSeries.HasSubst.X 1),
      hX0, hX1, MvPowerSeries.map_X, MvPowerSeries.map_X]
  have hBf : B = fadd g e' (X0 ^ l ^ i) (X1 ^ l ^ i) := by
    rw [hB, hmapF, PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.of_constantCoeff_zero hs0),
      map_add, PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.X 0),
      PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.X 1), hX0, hX1,
      MvPowerSeries.expand_X, MvPowerSeries.expand_X]
    rfl
  have hBeq : PowerSeries.subst B g
      = PowerSeries.subst (X0 ^ l ^ i) g + PowerSeries.subst (X1 ^ l ^ i) g := by
    rw [hBf]
    exact Pts.l_fadd hlog' (by rw [map_pow, hX00, zero_pow hn]) (by rw [map_pow, hX10, zero_pow hn])
  have hbe : be0 f e (frobOp σ l i f) X0 X1 = PowerSeries.subst A g - PowerSeries.subst B g := by
    unfold be0
    rw [← hF, hsX F hF0, hsX X0 hX00, hsX X1 hX10, hBeq]
    abel
  rw [hbe]
  exact key

end GlobalTheory.Honda
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
open Classical

theorem _root_.GlobalTheory.T.parahoric_hecke_sum_term_at_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ∀ (s : Finset D') (j : GL (A ⊕ D') k), j ∈ parahoric k A D' → ∀ d : kˣ, (d : k) = j.1.toBlocks₂₂.det → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, (InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) → ((ξ d * (ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = datum ξ x) ∧ (¬ InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) → datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = 0) := by
  first | exact @GlobalTheory.ParHeckeTarget.coset_term | exact GlobalTheory.ParHeckeTarget.coset_term | (intros; apply GlobalTheory.ParHeckeTarget.coset_term <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
open Classical

theorem _root_.GlobalTheory.T.card_filter_parahoric_cosets_eq_schur_count : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D') (R : Finset (GL (A ⊕ D') k)) d, IsReps (GlobalTheory.ZonalCellDecomposition.mtor ϖ (indic s)) R d → ∀ RK, IsRepsK (GlobalTheory.GLDoubling.torusElt k D' ϖ (indic s)) RK → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, InSupp x → (R.filter fun j => InSupp (((j * GlobalTheory.ZonalCellDecomposition.mtor ϖ (indic s))⁻¹).1 * x)).card = (RK.filter fun g => ∀ i l, ((g⁻¹).1 * schur x) i l ∈ 𝒪[k]).card := by
  exact @GlobalTheory.ParHeckeTarget.card_filter_eq
end

section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory

theorem symEdge_span_eq_top : ∀ (k : Type) [Field k] (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → ∀ (a : Fin n → Fin n → k), (∀ i j, symEdge ρ κ i j → a i j ≠ 0) → ∀ (V : Submodule k (Fin n → k)), V ≠ ⊥ → (∀ w ∈ V, (fun j => ∑ i, if symEdge ρ κ i j then a i j * w i else 0) ∈ V) → (∀ i j : Fin n, i < j → ¬(ρ ≤ i.val ∧ i.val < ρ + κ ∧ j.val = ρ + κ) → ∀ w ∈ V, Pi.single i (w j) ∈ V) → V = ⊤ := by
  intro k _ n ρ κ hn hρ a ha V hV hT hU
  have hsc : ∀ (i : Fin n) (c : k), c ≠ 0 → Pi.single i c ∈ V → Pi.single i (1 : k) ∈ V := by
    intro i c hc h
    have e : c⁻¹ • Pi.single i c = Pi.single i (1 : k) := by
      ext j; by_cases hj : j = i <;> simp [hj, hc]
    rw [← e]; exact V.smul_mem _ h
  let i0 : Fin n := ⟨0, by omega⟩
  have h0 : Pi.single i0 (1 : k) ∈ V := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
    by_cases hex : ∃ j : Fin n, 0 < j.val ∧ w j ≠ 0
    · obtain ⟨j, hj, hwj⟩ := hex
      exact hsc i0 (w j) hwj (hU i0 j (Fin.lt_def.2 hj) (by simp [i0]; omega) w hw)
    · push_neg at hex
      have hwe : w = Pi.single i0 (w i0) := by
        funext j
        by_cases hj : j = i0
        · subst hj; simp
        · have : 0 < j.val := by
            rcases Nat.eq_zero_or_pos j.val with h | h
            · exact absurd (Fin.ext h) hj
            · exact h
          rw [hex j this, Pi.single_eq_of_ne hj]
      have hne : w i0 ≠ 0 := fun h => hw0 (by rw [hwe, h, Pi.single_zero])
      exact hsc i0 _ hne (hwe ▸ hw)
  have hstep : ∀ x y : Fin n, symEdge ρ κ x y → (∀ j : Fin n, symEdge ρ κ x j → j = y) →
      Pi.single x (1 : k) ∈ V → Pi.single y (1 : k) ∈ V := by
    intro x y hxy huniq hx
    refine hsc y (a x y) (ha x y hxy) ?_
    have hu := hT _ hx
    convert hu using 1
    funext j
    rw [Finset.sum_eq_single x]
    · by_cases hj : j = y
      · subst hj; simp [hxy]
      · have : ¬ symEdge ρ κ x j := fun h => hj (huniq j h)
        simp [this, Pi.single_eq_of_ne hj]
    · intro i _ hi; simp [Pi.single_eq_of_ne hi]
    · simp
  have hwalk : ∀ t, t ≤ 2 * ρ → ∀ x : Fin n, x.val = (if t < ρ then t else t + κ) → Pi.single x (1 : k) ∈ V := by
    intro t
    induction t with
    | zero =>
      intro _ x hx
      have : x = i0 := Fin.ext (by simp [i0] at hx ⊢; split_ifs at hx <;> omega)
      rw [this]; exact h0
    | succ t ih =>
      intro ht y hy
      have hxlt : (if t < ρ then t else t + κ) < n := by split_ifs <;> omega
      let x : Fin n := ⟨_, hxlt⟩
      refine hstep x y ?_ ?_ (ih (by omega) x rfl)
      · unfold symEdge
        simp only [x]
        split_ifs at hy ⊢ <;> omega
      · intro j hj
        apply Fin.ext
        unfold symEdge at hj
        simp only [x] at hj
        split_ifs at hy hj <;> omega
  let last : Fin n := ⟨2 * ρ + κ, by omega⟩
  have hlast : Pi.single last (1 : k) ∈ V := hwalk (2 * ρ) le_rfl last (by simp [last]; omega)
  have hall : ∀ i : Fin n, Pi.single i (1 : k) ∈ V := by
    intro i
    by_cases hi : i = last
    · rw [hi]; exact hlast
    · have hlt : i < last := by
        rw [Fin.lt_def]; have := i.2; have : i.val ≠ 2 * ρ + κ := fun h => hi (Fin.ext h); simp [last]; omega
      have := hU i last hlt (by simp [last]; omega) _ hlast
      simpa using this
  rw [eq_top_iff, ← (Pi.basisFun k (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  exact hall i

end GlobalTheory
end

section

open Formalism.MainNotions.S
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.finrank_ker_le_hilbertSchmidtNormSq_sub_id : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (K : V →L[ℂ] V) (N : Submodule ℂ V), (∀ x ∈ N, K x = 0) → (Module.finrank ℂ N : ℝ) ≤ hsNormSq (K - ContinuousLinearMap.id ℂ V) := by
  first | exact @GlobalTheory.finrank_ker_le_hsNormSq_sub_id | exact GlobalTheory.finrank_ker_le_hsNormSq_sub_id | (intros; apply GlobalTheory.finrank_ker_le_hsNormSq_sub_id <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.irreducible_K_stable_finite_subspace : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S → ∀ v ∈ S, ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ ∀ B : H →L[ℂ] H, (∀ k ∈ Formalism.REAL.Kset ε, ∀ u, B (σ k u) = σ k (B u)) → ∀ y ∈ Y, B y ∈ Y) ∧ ∀ v, IsKFin ε σ v → Formalism.QuantumDeterminants.SmoothOnH (Formalism.REAL.Jm ε) (fun g => σ g v) := by
  first | exact @GlobalTheory.AdmUnitary.admissible_and_kFin_smooth | exact GlobalTheory.AdmUnitary.admissible_and_kFin_smooth | (intros; apply GlobalTheory.AdmUnitary.admissible_and_kFin_smooth <;> assumption)
end

end

section

@[expose] public section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

theorem _root_.GlobalTheory.T.symEdge_stable_submodule_eq_top : ∀ (k : Type) [Field k] (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → ∀ (a : Fin n → Fin n → k), (∀ i j, symEdge ρ κ i j → a i j ≠ 0) → ∀ (V : Submodule k (Fin n → k)), V ≠ ⊥ → (∀ w ∈ V, (fun j => ∑ i, if symEdge ρ κ i j then a i j * w i else 0) ∈ V) → (∀ i j : Fin n, i < j → ¬(ρ ≤ i.val ∧ i.val < ρ + κ ∧ j.val = ρ + κ) → ∀ w ∈ V, Pi.single i (w j) ∈ V) → V = ⊤ := by
  first | exact @GlobalTheory.symEdge_span_eq_top | exact GlobalTheory.symEdge_span_eq_top | (intros; apply GlobalTheory.symEdge_span_eq_top <;> assumption)

end
end
