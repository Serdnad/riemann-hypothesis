module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle266
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle261
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle267
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle269
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle270
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.approximate_identity_exists : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure], ∃ φ : ℕ → Mat n → ℝ, (∀ k, IsTest (φ k)) ∧ (∀ k y, 0 ≤ φ k y) ∧ (∀ k, ∫ y : G n, φ k y.val ∂μ = 1) ∧ ∀ N ∈ 𝓝 (1 : G n), ∀ᶠ k in atTop, ∀ y : G n, φ k y.val ≠ 0 → y ∈ N := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.exists_mollifiers | exact GlobalTheory.CompanionTheory.PresSobA.exists_mollifiers | (intros; apply GlobalTheory.CompanionTheory.PresSobA.exists_mollifiers <;> assumption)
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.mollification_evaluation_continuous : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → ∀ z ∈ GLs n, ∃ L : Lp V 2 μ →L[ℝ] V, ∀ x : Lp V 2 μ, L x = Mol μ φ (⇑x) z := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.MolBounded.mol_bounded | exact GlobalTheory.CompanionTheory.PresSobA.MolBounded.mol_bounded | (intros; apply GlobalTheory.CompanionTheory.PresSobA.MolBounded.mol_bounded <;> assumption)
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.mollification_differentiable : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → ∀ x : Lp V 2 μ, ∀ z ∈ GLs n, DifferentiableAt ℝ (Mol μ φ (⇑x)) z := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.mol_differentiableAt | exact GlobalTheory.CompanionTheory.PresSobA.mol_differentiableAt | (intros; apply GlobalTheory.CompanionTheory.PresSobA.mol_differentiableAt <;> assumption)
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.matrix_exp_curve_derivative : ∀ (n : ℕ) (X : Mat n), Continuous (expC X) ∧ ∀ t : ℝ, HasDerivAt (fun s : ℝ => (expC X s).val) ((expC X t).val * X) t := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.ExpCurve.expC_continuous_hasDerivAt | exact GlobalTheory.CompanionTheory.PresSobA.ExpCurve.expC_continuous_hasDerivAt | (intros; apply GlobalTheory.CompanionTheory.PresSobA.ExpCurve.expC_continuous_hasDerivAt <;> assumption)
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

variable {l : ℕ} [Fact l.Prime]

theorem norm_pow_sub_pow_le {a b : ℂ_[l]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a ^ n * (a - b) + (a ^ n - b ^ n) * b := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hb).trans ih

theorem norm_pow_prime_sub_le {a b : ℂ_[l]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) {s : ℝ}
    (hl : ‖(l : ℂ_[l])‖ ≤ s) (hs : ‖a - b‖ ≤ s) : ‖a ^ l - b ^ l‖ ≤ s * ‖a - b‖ := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hl
  have hbp : ∀ n : ℕ, ‖b ^ n‖ ≤ 1 := fun n => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hb
  have hap : ∀ n : ℕ, ‖a ^ n‖ ≤ 1 := fun n => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have e : a ^ l - b ^ l = (∑ i ∈ Finset.range l, a ^ i * b ^ (l - 1 - i)) * (a - b) :=
    (geom_sum₂_mul a b l).symm
  have e2 : (∑ i ∈ Finset.range l, a ^ i * b ^ (l - 1 - i))
      = (∑ i ∈ Finset.range l, (a ^ i * b ^ (l - 1 - i) - b ^ (l - 1))) + (l : ℂ_[l]) * b ^ (l - 1) := by
    simp [Finset.sum_sub_distrib]
  have h1 : ‖∑ i ∈ Finset.range l, (a ^ i * b ^ (l - 1 - i) - b ^ (l - 1))‖ ≤ s := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hs0 fun i hi => ?_
    have hi' : i ≤ l - 1 := by
      have := Finset.mem_range.1 hi
      omega
    have e3 : a ^ i * b ^ (l - 1 - i) - b ^ (l - 1) = (a ^ i - b ^ i) * b ^ (l - 1 - i) := by
      rw [sub_mul, ← pow_add, Nat.add_sub_cancel' hi']
    rw [e3, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hbp _)).trans
      ((norm_pow_sub_pow_le ha hb i).trans hs)
  have h2 : ‖(l : ℂ_[l]) * b ^ (l - 1)‖ ≤ s := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hbp _)).trans hl
  rw [e, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [e2]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

theorem norm_pow_prime_pow_sub_le {a b : ℂ_[l]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) {s : ℝ}
    (hs1 : s ≤ 1) (hl : ‖(l : ℂ_[l])‖ ≤ s) (hs : ‖a - b‖ ≤ s) (n : ℕ) :
    ‖a ^ l ^ n - b ^ l ^ n‖ ≤ s ^ n * ‖a - b‖ := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hl
  induction n with
  | zero => simp
  | succ n ih =>
    have ha' : ‖a ^ l ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
    have hb' : ‖b ^ l ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hb
    have hle : ‖a ^ l ^ n - b ^ l ^ n‖ ≤ s :=
      ih.trans ((mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs0 hs1)).trans hs)
    have h := norm_pow_prime_sub_le ha' hb' hl hle
    rw [← pow_mul, ← pow_mul, ← pow_succ] at h
    refine h.trans ?_
    rw [pow_succ, mul_comm (s ^ n) s, mul_assoc]
    exact mul_le_mul_of_nonneg_left ih hs0

theorem isClosed_range_finExt (K : FinExt l) :
    IsClosed (Set.range fun y : ↥K.1 => omC (l := l) (y : Om l)) := by
  haveI := K.2
  let L : ↥K.1 →ₗ[ℚ_[l]] ℂ_[l] :=
    (IsScalarTower.toAlgHom ℚ_[l] (Om l) ℂ_[l]).toLinearMap ∘ₗ K.1.val.toLinearMap
  have h := Submodule.closed_of_finiteDimensional (LinearMap.range L)
  have e : (Set.range fun y : ↥K.1 => omC (l := l) (y : Om l)) = (LinearMap.range L : Set ℂ_[l]) := by
    ext z
    rfl
  rw [e]
  exact h

theorem exists_int_of_norm_le (K : FinExt l) (y : ↥K.1) (hy : ‖(y : Om l)‖ ≤ 1) :
    ∃ c : ↥(OL K), (c : ↥K.1) = y :=
  ⟨(GlobalTheory.CompanionTheory.LTHodge.CharEx.intEquiv K).symm
    ⟨y, (GlobalTheory.CompanionTheory.LTHodge.CharEx.mem_integer_iff K y).2 hy⟩, rfl⟩

theorem sh_root_near_integer : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ), 0 < f → qOf π = l ^ f →
    ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ → ‖oc K π‖ < 1 → π ≠ 0 → ∀ (x : Tl l) (c : ↥(OL K)), x ^ l ^ f = x →
    ‖sh x - oc K c‖ ≤ ‖oc K π‖ → ∃ c' : ↥(OL K), sh x = oc K (c + π * c') := by
  intro l _ K π f hf _ hl hπ1 hπ0 x c hx hc
  set s := ‖oc K π‖ with hsdef
  have hs0 : 0 ≤ s := norm_nonneg _
  have hζ1 : ‖sh x‖ ≤ 1 := norm_sh_le_one x
  have hc1 : ‖oc K c‖ ≤ 1 := norm_oc_le_one K c
  have hfix1 : sh x ^ l ^ f = sh x := by rw [← sh_pow, hx]
  have hfix : ∀ m : ℕ, sh x ^ (l ^ f) ^ m = sh x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, hfix1]
  have hdist : ‖oc K c - sh x‖ ≤ s := by rw [norm_sub_rev]; exact hc
  have hbound : ∀ m : ℕ, ‖oc K (c ^ (l ^ f) ^ m) - sh x‖ ≤ s ^ m := by
    intro m
    have h := norm_pow_prime_pow_sub_le hc1 hζ1 hπ1.le hl hdist (f * m)
    rw [pow_mul, hfix m, ← map_pow] at h
    refine h.trans ?_
    have h1 : s ^ (f * m) ≤ s ^ m :=
      pow_le_pow_of_le_one hs0 hπ1.le (Nat.le_mul_of_pos_left m hf)
    exact (mul_le_of_le_one_right (pow_nonneg hs0 _) (hdist.trans hπ1.le)).trans h1
  have hlim : Filter.Tendsto (fun m : ℕ => oc K (c ^ (l ^ f) ^ m)) Filter.atTop (nhds (sh x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) hbound
      (tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hπ1)
  have hmem : sh x ∈ Set.range fun y : ↥K.1 => omC (l := l) (y : Om l) :=
    (isClosed_range_finExt K).mem_of_tendsto hlim
      (Filter.Eventually.of_forall fun m => ⟨((c ^ (l ^ f) ^ m : ↥(OL K)) : ↥K.1), rfl⟩)
  obtain ⟨y, hy⟩ := hmem
  have hy : omC (l := l) (y : Om l) = sh x := hy
  have hcK : oc K c = omC (l := l) ((c : ↥K.1) : Om l) := rfl
  have hπK : oc K π = omC (l := l) ((π : ↥K.1) : Om l) := rfl
  have hπ0' : (π : ↥K.1) ≠ 0 := fun h => hπ0 (Subtype.ext h)
  have hπ0'' : ((π : ↥K.1) : Om l) ≠ 0 := fun h => hπ0' (Subtype.ext h)
  have hnum : ‖((y - (c : ↥K.1) : ↥K.1) : Om l)‖ ≤ ‖((π : ↥K.1) : Om l)‖ := by
    have : ‖sh x - oc K c‖ = ‖((y - (c : ↥K.1) : ↥K.1) : Om l)‖ := by
      rw [← hy, hcK, ← map_sub, norm_omC]
      rfl
    rw [← this, ← norm_omC, ← hπK]
    exact hc
  have hq : ‖(((y - (c : ↥K.1)) / (π : ↥K.1) : ↥K.1) : Om l)‖ ≤ 1 := by
    have e : (((y - (c : ↥K.1)) / (π : ↥K.1) : ↥K.1) : Om l)
        = ((y - (c : ↥K.1) : ↥K.1) : Om l) / ((π : ↥K.1) : Om l) := rfl
    rw [e, norm_div]
    exact div_le_one_of_le₀ hnum (norm_nonneg _)
  obtain ⟨c', hc'⟩ := exists_int_of_norm_le K _ hq
  refine ⟨c', ?_⟩
  have hsum : ((c + π * c' : ↥(OL K)) : ↥K.1) = y := by
    have : ((c + π * c' : ↥(OL K)) : ↥K.1) = (c : ↥K.1) + (π : ↥K.1) * (c' : ↥K.1) := rfl
    rw [this, hc']
    field_simp
    ring
  rw [← hy]
  show _ = omC (l := l) (((c + π * c' : ↥(OL K)) : ↥K.1) : Om l)
  rw [hsum]

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv

variable {l : ℕ} [Fact l.Prime]

theorem continuous_omC : Continuous (omC (l := l)) :=
  (AddMonoidHomClass.isometry_of_norm (omC (l := l)) norm_omC).continuous

theorem tail_le (K : FinExt l) (c : ℕ → ↥(OL K)) (y x : Om l) (hy : ‖omC y‖ ≤ 1)
    (hs : HasSum (fun k : ℕ => ((c k : ↥K.1) : Om l) * y ^ k) x) (D : ℕ) :
    ‖omC x - ∑ i ∈ Finset.range D, oc K (c i) * omC y ^ i‖ ≤ ‖omC y‖ ^ D := by
  have ht : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, oc K (c i) * omC y ^ i)
      Filter.atTop (nhds (omC x)) := by
    have h1 := (continuous_omC (l := l)).continuousAt.tendsto.comp hs.tendsto_sum_nat
    refine h1.congr fun N => ?_

    simp only [Function.comp, map_sum, map_mul, map_pow]
    rfl
  have h2 := (ht.sub_const (∑ i ∈ Finset.range D, oc K (c i) * omC y ^ i)).norm
  refine le_of_tendsto h2 ?_
  filter_upwards [Filter.eventually_ge_atTop D] with N hN
  rw [← Finset.sum_Ico_eq_sub _ hN]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k hk => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) (norm_oc_le_one K _)).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hy (Finset.mem_Ico.1 hk).1)

theorem norm_read {ρ : ℝ} (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) (a y : Tl l) (b : ℕ → Tl l)
    (A Y : ℂ_[l]) (B : ℕ → ℂ_[l]) (D : ℕ) (hY : ‖Y‖ ≤ 1) (hA : ‖sh a - A‖ ≤ ρ)
    (hy : ‖sh y - Y‖ ≤ ρ) (hb : ∀ i, ‖sh (b i) - B i‖ ≤ ρ) :
    ‖a - ∑ i ∈ Finset.range D, b i * y ^ i‖ ≤
      max ρ ‖A - ∑ i ∈ Finset.range D, B i * Y ^ i‖ := by
  have h1 : ‖sh (∑ i ∈ Finset.range D, b i * y ^ i) - ∑ i ∈ Finset.range D, B i * Y ^ i‖ ≤ ρ :=
    near_sum hρ _ fun i _ => near_mul (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hY)
      (hb i) (near_pow hρ hY hy i)
  have h2 := near_sub hρ hA h1
  rw [norm_eq_norm_sh]
  set x := a - ∑ i ∈ Finset.range D, b i * y ^ i
  set W := A - ∑ i ∈ Finset.range D, B i * Y ^ i
  have e : sh x = (sh x - W) + W := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max h2 le_rfl)

theorem pow_read (N : ℕ) (a y : Tl l) (b : ℕ → Tl l) (D : ℕ) :
    (a - ∑ i ∈ Finset.range D, b i * y ^ i) ^ l ^ N =
      a ^ l ^ N - ∑ i ∈ Finset.range D, b i ^ l ^ N * (y ^ l ^ N) ^ i := by
  rw [sub_pow_char_pow, sum_pow_char_pow]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i]

theorem pow_compat {f : ℕ} {u : ℕ → Tl l} (hu : ∀ n, u (n + 1) ^ l ^ f = u n) (n m : ℕ) :
    u (n + m) ^ l ^ (f * m) = u n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, mul_add, mul_one, add_comm (f * m) f, pow_add, pow_mul, hu, ih]

theorem pow_fixed {f : ℕ} {x : Tl l} (hx : x ^ l ^ f = x) (m : ℕ) : x ^ l ^ (f * m) = x := by
  induction m with
  | zero => simp
  | succ m ih => rw [mul_add, mul_one, add_comm (f * m) f, pow_add, pow_mul, hx, ih]

theorem exists_pow_le {f : ℕ} (hf : 0 < f) {ρ ε : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (hε : 0 < ε) :
    ∃ m, 2 ≤ m ∧ ρ ^ l ^ (f * m) ≤ ε := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε h1
  refine ⟨N + 2, by omega, (pow_le_pow_of_le_one h0 h1.le ?_).trans hN.le⟩
  have h2 : N + 2 < l ^ (N + 2) := Nat.lt_pow_self (Fact.out : l.Prime).one_lt
  have h3 : l ^ (N + 2) ≤ l ^ (f * (N + 2)) :=
    Nat.pow_le_pow_right (Fact.out : l.Prime).pos (Nat.le_mul_of_pos_left _ hf)
  omega

theorem galdiv : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (z : ℕ → Om l) (f : ℕ), 0 < f →
    ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ → ‖oc K π‖ < 1 →
    (∀ n, ‖omC (z n)‖ < 1) → (∀ n, 2 ≤ n → ‖oc K π‖ < ‖omC (z n)‖) →
    ∀ (u : ℕ → Tl l), (∀ n, u (n + 1) ^ l ^ f = u n) → (∀ n, ‖sh (u n) - omC (z n)‖ ≤ ‖oc K π‖) →
    ∀ (r₀ : ↥(OL K) →+* Tl l), (∀ c, r₀ c ^ l ^ f = r₀ c) → (∀ c, ‖sh (r₀ c) - oc K c‖ ≤ ‖oc K π‖) →
    (∀ n, u n ≠ 0) → ∀ (g : GQ l) (c : ℕ → ↥(OL K)),
    (∀ n, HasSum (fun k : ℕ => ((c k : ↥K.1) : Om l) * z n ^ k) (g (z n))) → ∀ n D : ℕ,
    u n ^ D ∣ actT g (u n) - ∑ i ∈ Finset.range D, r₀ (c i) * u n ^ i := by
  intro l _ K π z f hf hl hπ hz1 hz2 u hu hun r₀ hr hrn hu0 g c hs n D
  rw [GroundTheory.PAdicHodge.preTilt_dvd_iff_norm_le, norm_pow]
  set ρ := ‖oc K π‖ with hρdef
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hε : 0 < ‖u n‖ ^ D := pow_pos (norm_pos_iff.2 (hu0 n)) D
  obtain ⟨m, hm, hmρ⟩ := exists_pow_le (l := l) hf hρ0 hπ hε
  set k := n + m with hk
  have hk2 : 2 ≤ k := by omega
  have hzk : ‖omC (z k)‖ ≤ 1 := (hz1 k).le
  have hnorm : ‖omC (z k)‖ ≤ ‖u k‖ := by
    by_contra hlt
    push_neg at hlt
    have e : omC (z k) = sh (u k) - (sh (u k) - omC (z k)) := by ring
    have h3 : ‖omC (z k)‖ ≤ max ‖sh (u k)‖ ρ := by
      conv_lhs => rw [e, sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le_max le_rfl (by rw [norm_neg]; exact hun k))
    rcases le_max_iff.1 h3 with h4 | h4
    · rw [← norm_eq_norm_sh] at h4; linarith
    · linarith [hz2 k hk2]
  have hA : ‖sh (actT g (u k)) - omC (g (z k))‖ ≤ ρ := by
    rw [sh_actT, ← galCp_omC, ← map_sub, norm_galCp]
    exact hun k
  have hread := norm_read hl (actT g (u k)) (u k) (fun i => r₀ (c i)) (omC (g (z k))) (omC (z k))
    (fun i => oc K (c i)) D hzk hA (hun k) (fun i => hrn _)
  have htail := tail_le K c (z k) (g (z k)) hzk (hs k) D
  have hx : ‖actT g (u k) - ∑ i ∈ Finset.range D, r₀ (c i) * u k ^ i‖ ≤ max ρ (‖u k‖ ^ D) :=
    hread.trans (max_le_max le_rfl (htail.trans (pow_le_pow_left₀ (norm_nonneg _) hnorm D)))
  have hpow := pow_read (f * m) (actT g (u k)) (u k) (fun i => r₀ (c i)) D
  have hc : u k ^ l ^ (f * m) = u n := pow_compat hu n m
  have ha : actT g (u k) ^ l ^ (f * m) = actT g (u n) := by rw [← map_pow, hc]
  simp only [pow_fixed (hr _) m, hc, ha] at hpow
  rw [← hpow, norm_pow]
  have hun' : ‖u k‖ ^ l ^ (f * m) = ‖u n‖ := by rw [← norm_pow, hc]
  refine (pow_le_pow_left₀ (norm_nonneg _) hx _).trans ?_
  rcases le_total ρ (‖u k‖ ^ D) with h | h
  · rw [max_eq_right h, ← pow_mul, mul_comm, pow_mul, hun']
  · rw [max_eq_left h]; exact hmρ

end GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem isUnit_BdRp_of_thB {l : ℕ} [Fact l.Prime] {u : Formalism.Per6.BdRp l} (h : thB l u ≠ 0) :
    IsUnit u := by
  change IsUnit (show BDeRhamPlus (GroundTheory.PAdicHodge.normInteger ℂ_[l]) l from u)
  by_contra hy
  have h2 := (IsLocalRing.mem_maximalIdeal _).2 hy
  rw [GroundTheory.PAdicHodge.IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker] at h2
  exact h h2

theorem eq_of_pow_eq_self_of_thB_eq {l : ℕ} [Fact l.Prime] {q : ℕ} (hq : 2 ≤ q)
    {a b : Formalism.Per6.BdRp l} (ha : a ^ q = a) (hb : b ^ q = b) (hab : thB l a = thB l b) :
    a = b := by
  set S : Formalism.Per6.BdRp l := ∑ i ∈ Finset.range q, a ^ i * b ^ (q - 1 - i) with hS
  have hkey : (a - b) * (S - 1) = 0 := by
    have h1 : (a - b) * S = a ^ q - b ^ q := (Commute.all a b).mul_geom_sum₂ q
    rw [mul_sub, h1, ha, hb, mul_one, sub_self]
  have hθS : thB l S = (q : ℂ_[l]) * thB l a ^ (q - 1) := by

    rw [hS, map_sum, Finset.sum_congr rfl (g := fun _ => thB l a ^ (q - 1))]
    · simp
    · intro i hi
      have hi' : i ≤ q - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.1 hi)
      rw [map_mul, map_pow, map_pow, ← hab, ← pow_add, Nat.add_sub_cancel' hi']
  have hζ : thB l a ^ q = thB l a := by rw [← map_pow, ha]
  have hne : thB l (S - 1) ≠ 0 := by
    rw [map_sub, map_one, hθS]
    by_cases h0 : thB l a = 0
    · rw [h0, zero_pow (by omega)]
      simp
    · have h1 : thB l a ^ (q - 1) = 1 := by
        have e : thB l a ^ (q - 1) * thB l a = 1 * thB l a := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega), hζ, one_mul]
        exact mul_right_cancel₀ h0 e
      rw [h1, mul_one, sub_ne_zero]
      exact_mod_cast (by omega : q ≠ 1)
  have hu := isUnit_BdRp_of_thB hne
  exact sub_eq_zero.1 ((hu.mul_left_eq_zero).1 hkey)

theorem tch_eq_rB_of_sh_eq : ∀ {l : ℕ} [Fact l.Prime] (q : ℕ), 2 ≤ q → l ∣ q → ∀ (x : Tl l) (y : Om l),
    x ^ q = x → y ^ q = y → sh x = omC y → tch l x = rB l y := by
  intro l _ q hq _ x y hx hy hxy
  refine eq_of_pow_eq_self_of_thB_eq hq ?_ ?_ ?_
  · rw [← tch_pow, hx]
  · rw [← map_pow, hy]
  · rw [thB_tch, thB_rB, hxy, omC_apply]

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.exists_lattice_bound_integers : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K], ∃ M : ℕ, ∀ (k : ℕ) (a : OK l K), Lat.pk l k (Lat.kP l K a) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatCOK.exists_uniform_mem_sub | exact GlobalTheory.CompanionTheory.LatCOK.exists_uniform_mem_sub | (intros; apply GlobalTheory.CompanionTheory.LatCOK.exists_uniform_mem_sub <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

theorem _root_.GlobalTheory.T.local_character_finite_extension : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (μ : G E Ω →* (Qbar l)ˣ), Continuous μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
    ∃ (LL' : FinExt l) (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ), Bw.LL.1 ≤ LL'.1 ∧
      IsModel Bw ((rk1 μ).comp (Dec (F := E) A).subtype) LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) ∧
      (∀ g, ((ψ g : ↥LL'.1) : Qbar l) = ((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l)) ∧
      Continuous (fun g => ((ψ g : ↥LL'.1) : Qbar l)) ∧ ∀ g, ‖((ψ g : ↥LL'.1) : Qbar l)‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeChar.exists_unit_model | exact GlobalTheory.CompanionTheory.HeckeChar.exists_unit_model | (intros; apply GlobalTheory.CompanionTheory.HeckeChar.exists_unit_model <;> assumption)
end
end

section


theorem _root_.GlobalTheory.T.section_norm_bound : PositivityTheory.RgBcC.Fc.SecBound := by
  first | exact @GlobalTheory.CompanionTheory.SecBd.secBound_main | exact GlobalTheory.CompanionTheory.SecBd.secBound_main | (intros; apply GlobalTheory.CompanionTheory.SecBd.secBound_main <;> assumption)
end
