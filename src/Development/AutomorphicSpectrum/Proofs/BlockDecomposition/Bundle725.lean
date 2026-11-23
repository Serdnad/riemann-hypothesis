module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle716
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle600
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle602
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle601
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle674
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle710
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle706
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle686
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle701
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle724
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle723
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle689
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle015

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilMaj

theorem schwartz_col_bound {T : Type} [Fintype T] {M n : ℕ} (f : SchwartzMap (T → Fin M → Fin n → ℂ) ℂ)
    (P : ℝ) (hP : 1 ≤ P) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : T → Fin M → Fin n → ℂ, ‖b‖ ≤ P * ‖a‖ →
      ‖f a‖ ≤ C * ∏ j : Fin n, ((1 + ‖fun τ i => b τ i j‖) ^ N)⁻¹ := by
  obtain ⟨C0, hC0, hC0'⟩ : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ a, (1 + ‖a‖) ^ (N * n) * ‖f a‖ ≤ C0 := by
    refine ⟨(2 : ℝ) ^ (N * n, 0).1 * ((Finset.Iic (N * n, 0)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f,
      by positivity, fun a => ?_⟩
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N * n, 0)) (k := N * n) (n := 0)
      le_rfl le_rfl f a
    simpa using h
  refine ⟨C0 * P ^ (N * n), by positivity, fun a b hab => ?_⟩
  have hP0 : 0 < P := by linarith
  have ha : 0 < 1 + ‖a‖ := by positivity
  have hb : 0 < 1 + ‖b‖ := by positivity
  have h1 : 1 + ‖b‖ ≤ P * (1 + ‖a‖) := by nlinarith [norm_nonneg a]
  have hcol : ∀ j, ‖fun τ i => b τ i j‖ ≤ ‖b‖ := fun j => by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun τ => ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    exact (norm_le_pi_norm (b τ i) j).trans ((norm_le_pi_norm (b τ) i).trans (norm_le_pi_norm b τ))
  have h2 : ((1 + ‖b‖) ^ (N * n))⁻¹ ≤ ∏ j : Fin n, ((1 + ‖fun τ i => b τ i j‖) ^ N)⁻¹ := by
    have e : ((1 + ‖b‖) ^ (N * n))⁻¹ = ∏ _j : Fin n, ((1 + ‖b‖) ^ N)⁻¹ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, pow_mul]
    rw [e]
    refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun j _ => ?_
    have : 0 < 1 + ‖fun τ i => b τ i j‖ := by positivity
    refine inv_anti₀ (by positivity) (pow_le_pow_left₀ this.le ?_ N)
    linarith [hcol j]
  have h3 : ‖f a‖ ≤ C0 * ((1 + ‖a‖) ^ (N * n))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact hC0' a
  have h4 : ((1 + ‖a‖) ^ (N * n))⁻¹ ≤ P ^ (N * n) * ((1 + ‖b‖) ^ (N * n))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity), ← mul_pow, mul_comm (1 + ‖a‖)]
    exact pow_le_pow_left₀ hb.le h1 _
  calc ‖f a‖ ≤ C0 * ((1 + ‖a‖) ^ (N * n))⁻¹ := h3
    _ ≤ C0 * (P ^ (N * n) * ((1 + ‖b‖) ^ (N * n))⁻¹) := by gcongr
    _ = C0 * P ^ (N * n) * ((1 + ‖b‖) ^ (N * n))⁻¹ := by ring
    _ ≤ _ := by gcongr

variable {D : D7}

theorem mt_mul_inv (V : HSp D) (y : GA D V) :
    (HMul.hMul (Formalism.L2.Theta.mt V y) (Formalism.L2.Theta.mt V y⁻¹) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = 1 := by
  have h : (Formalism.L2.Theta.matHom V y) * (Formalism.L2.Theta.matHom V y⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  exact congrArg Units.val h

theorem compAt_mul' (θ : InfFam D) (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D k n) = HMul.hMul (compAt θ τ x) (compAt θ τ y) :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem real_compare {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (n : ℕ) (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ y ∈ C₁, ∀ x : Mx D V.rank n,
      ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin V.rank → Fin n → ℂ)‖ ≤
        P * ‖(fun τ i j => compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j :
          D.what₂.Tau → Fin V.rank → Fin n → ℂ)‖ := by
  let B : GA D V → (D.what₂.Tau → Fin V.rank → Fin V.rank → ℂ) := fun y τ i k => compAt θ τ (Formalism.L2.Theta.mt V y) i k
  have hB : Continuous B := by
    refine continuous_pi fun τ => continuous_pi fun i => continuous_pi fun k => ?_
    exact ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp (GlobalTheory.RealWeil.continuous_mt V).1).matrix_elem i k
  obtain ⟨R, hR⟩ := hC₁.exists_bound_of_continuousOn hB.continuousOn
  refine ⟨1 + V.rank * |R|, by have := abs_nonneg R; nlinarith [Nat.cast_nonneg (α := ℝ) V.rank, mul_nonneg (Nat.cast_nonneg (α := ℝ) V.rank) (abs_nonneg R)], fun y hy x => ?_⟩
  set u : D.what₂.Tau → Fin V.rank → Fin n → ℂ :=
    fun τ i j => compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j with hu
  have hx : ∀ τ, compAt θ τ x = HMul.hMul (compAt θ τ (Formalism.L2.Theta.mt V y))
      (compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)) := fun τ => by
    rw [← compAt_mul', ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
  have hN : 0 ≤ (1 + V.rank * |R|) * ‖u‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg hN).2 fun τ => (pi_norm_le_iff_of_nonneg hN).2 fun i =>
    (pi_norm_le_iff_of_nonneg hN).2 fun j => ?_
  rw [hx τ, Matrix.mul_apply]
  have hk : ∀ k, ‖compAt θ τ (Formalism.L2.Theta.mt V y) i k * compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) k j‖ ≤ |R| * ‖u‖ := fun k => by
    rw [norm_mul]
    have e1 : ‖compAt θ τ (Formalism.L2.Theta.mt V y) i k‖ ≤ |R| :=
      ((norm_le_pi_norm (B y τ i) k).trans ((norm_le_pi_norm (B y τ) i).trans (norm_le_pi_norm (B y) τ))).trans
        ((hR y hy).trans (le_abs_self R))
    have e2 : ‖compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) k j‖ ≤ ‖u‖ :=
      (norm_le_pi_norm (u τ k) j).trans ((norm_le_pi_norm (u τ) k).trans (norm_le_pi_norm u τ))
    exact mul_le_mul e1 e2 (norm_nonneg _) (abs_nonneg _)
  calc _ ≤ ∑ k, ‖compAt θ τ (Formalism.L2.Theta.mt V y) i k * compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin V.rank, |R| * ‖u‖ := Finset.sum_le_sum fun k _ => hk k
    _ = V.rank * |R| * ‖u‖ := by simp [Finset.sum_const, mul_assoc]
    _ ≤ _ := by nlinarith [norm_nonneg u]



theorem finite_compare (V : HSp D) (n : ℕ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact L ∧
      ∀ y ∈ C₁, ∀ x : Mx D V.rank n,
        g (fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j)) ≠ 0 →
        ∀ j, (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) ∈ L := by
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  have hS : IsCompact (tsupport g) := hg.2
  let Φ : GA D V × (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) →
      (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun p i j => ∑ k, finPart D (Formalism.L2.Theta.mt V p.1 i k) * p.2 k j
  have hΦ : Continuous Φ := by
    refine continuous_pi fun i => continuous_pi fun j => continuous_finsetSum _ fun k _ => ?_
    refine Continuous.mul ?_ ?_
    · exact GlobalTheory.SchwartzSch.continuous_finPart'.comp
        (((GlobalTheory.RealWeil.continuous_mt V).1.comp continuous_fst).matrix_elem i k)
    · exact (continuous_apply j).comp ((continuous_apply k).comp continuous_snd)
  have hK := (hC₁.prod hS).image hΦ
  let col : Fin n → (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) →
      Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun j w => Matrix.of fun i' _ => w i' j
  have hcol : ∀ j, Continuous (col j) := fun j =>
    continuous_pi fun i => continuous_pi fun _ => (continuous_apply j).comp (continuous_apply i)
  refine ⟨⋃ j, col j '' (Φ '' (C₁ ×ˢ tsupport g)), isCompact_iUnion fun j => hK.image (hcol j),
    fun y hy x hne j => Set.mem_iUnion.2 ⟨j, fun i j => finPart D (x i j),
      ⟨(y, fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j)),
        ⟨hy, subset_tsupport _ hne⟩, ?_⟩, rfl⟩⟩
  funext i j
  have e : (HMul.hMul (Formalism.L2.Theta.mt V y) (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) : Mx D V.rank n) = x := by
    rw [← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
  have e2 := congrFun (congrFun e i) j
  rw [Matrix.mul_apply] at e2
  show ∑ k, finPart D (Formalism.L2.Theta.mt V y i k) * finPart D _ = _

  rw [← e2, map_sum]
  exact Finset.sum_congr rfl fun k _ => ((finPart D).map_mul _ _).symm

theorem schwartz_translate_majorant : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ) (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ), g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ∀ (C₁ : Set (GA D V)), IsCompact C₁ → ∀ N : ℕ, ∃ (C : ℝ) (L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E))), IsCompact L ∧ ∀ y ∈ C₁, ∀ x : Mx D V.rank n, ‖f (fun τ i j => compAt θ τ (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D)) i j) * g (fun i j => finPart D ((HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D)) i j))‖ₑ ≤ ENNReal.ofReal C * ∏ j : Fin n, ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ (Matrix.of fun i' (_ : Fin 1) => x i' j) i 0‖) ^ N)⁻¹ * Set.indicator L (fun _ => (1 : ℝ)) (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j))) := by
  intro D θ hθ V n f g hg C₁ hC₁ N
  obtain ⟨P, hP, hPx⟩ := real_compare hθ V n C₁ hC₁
  obtain ⟨C, hC, hf⟩ := schwartz_col_bound f P hP N
  obtain ⟨L, hL, hLx⟩ := finite_compare V n g hg C₁ hC₁
  obtain ⟨G, hG⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  refine ⟨C * |G|, L, hL, fun y hy x => ?_⟩
  by_cases h0 : g (fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j)) = 0
  · have e : ∀ a : ℂ, ‖a * g (fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j))‖ₑ = 0 := fun a => by
      rw [h0, mul_zero, enorm_zero]
    exact (e _).le.trans zero_le
  · have hm := hLx y hy x h0
    have hb := hf _ _ (hPx y hy x)
    have hterm : ∀ j : Fin n, 0 ≤ ((1 + ‖fun τ i => compAt θ τ (Matrix.of fun i' (_ : Fin 1) => x i' j) i 0‖) ^ N)⁻¹ *
        Set.indicator L (fun _ => (1 : ℝ)) (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) := fun j => by
      rw [Set.indicator_of_mem (hm j)]
      positivity
    rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => hterm j,
      ← ENNReal.ofReal_mul (mul_nonneg hC (abs_nonneg G)), ← ofReal_norm_eq_enorm]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [Set.indicator_of_mem (hm _), mul_one]
    rw [norm_mul]
    calc _ ≤ (C * ∏ j : Fin n, ((1 + ‖fun τ i => compAt θ τ (Matrix.of fun i' (_ : Fin 1) => x i' j) i 0‖) ^ N)⁻¹) * |G| :=
          mul_le_mul hb ((hG _).trans (le_abs_self G)) (norm_nonneg _)
            (mul_nonneg hC (Finset.prod_nonneg fun j _ => by positivity))
      _ = _ := by ring

end GlobalTheory.CompanionTheory.WeilMaj
end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.LanglandsMultiseg

theorem langlandsMultisegments_of_clauses (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    (hSoc : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSocleGL k)
    (hSeg : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSegJacquet k)
    (hFree : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LOrderFree k)
    (hE : GlobalTheory.Published.LanglandsExhaustionGL) : GlobalTheory.Published.LanglandsMultisegments := by
  intro k _ _ _ _ _
  exact ⟨GlobalTheory.T.langlands_injective_of_socle hA (hSoc k) (hSeg k),
    fun 𝔪 𝔫 x y hd h₀ h₁ hy =>
      GlobalTheory.T.langlands_sum_subquotient_product hA (hSoc k) (hSeg k)
        (hFree k) (hE k) 𝔪 𝔫 x y hd h₀ h₁ hy⟩

end GlobalTheory.CompanionTheory.LanglandsMultiseg
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.partial_coefficient_heisenberg_expansion : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (h : G D n), pc M m ψ b₀ F (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * h) = ∫ x in m.𝓕, conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ξ)) * zc M m ψ b₀ F (M.nzx 0 x * h) ∂m.μ := by
  first | exact @GlobalTheory.CompanionTheory.FJE.PcShear.pc_sh | exact GlobalTheory.CompanionTheory.FJE.PcShear.pc_sh | (intros; apply GlobalTheory.CompanionTheory.FJE.PcShear.pc_sh <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fourier_jacobi_terms_summable : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ g : G D n, (∀ C : Set (G D n), IsCompact C → ∃ c : GlobalTheory.Eis.Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E → ℝ, Summable c ∧ ∀ g ∈ C, ∀ u, ‖Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)‖ ≤ c u) → ∃ t : GlobalTheory.Eis.Cosets (P D p) (GF D p) → ℝ, Summable t ∧ ∀ (q : GlobalTheory.Eis.Cosets (P D p) (GF D p)) (y : Mx D ρ p), Summable (fun η : Matrix (Fin ρ) (Fin p) D.host.E => ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y) * M.emb (q.out : GF D p) * g)‖) ∧ ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y) * M.emb (q.out : GF D p) * g)‖ ≤ t q := by
  first | exact @GlobalTheory.CompanionTheory.FJE.Domination.domination | exact GlobalTheory.CompanionTheory.FJE.Domination.domination | (intros; apply GlobalTheory.CompanionTheory.FJE.Domination.domination <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_fourier_jacobi_lattice_swap : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ThTwist → ∀ (χ' : (AE D)ˣ →* Circle), IsHeckeChar D χ' → ∀ θ : InfFam D, IsInfFam θ → ∀ Ω, IsTh ψ χ' θ b₀ m.μ Ω → ∀ (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ (g γ : _), γ ∈ GF D p → ∀ (T : Mx D ρ p × Mx D ρ p → Mx D ρ p × Mx D ρ p), (∀ y x : Mx D ρ p, ∃ z' : hermA D ρ, M.emb γ * (M.nzx 0 x * M.sh y) = M.nzx z' (T (y, x)).2 * M.sh (T (y, x)).1 * M.emb γ) → ∀ v : Mx D ρ p × Mx D ρ p, (∀ η : Matrix (Fin ρ) (Fin p) D.host.E, ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))‖ = ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + (T v).1) * M.emb γ * g)‖) ∧ (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))) * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) = GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (Ω γ) (T v) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.term_after | exact GlobalTheory.CompanionTheory.FJE.term_after | (intros; apply GlobalTheory.CompanionTheory.FJE.term_after <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.RhoSplit

theorem exists_lift {A B C : Type} [Group A] [Group B] [Group C] (φ : A →* C) (ι : B →* C)
    (hι : Function.Injective ι) (h : ∀ a, φ a ∈ ι.range) : ∃ ρ : A →* B, ∀ a, φ a = ι (ρ a) := by
  refine ⟨((MonoidHom.ofInjective hι).symm.toMonoidHom).comp (φ.codRestrict ι.range h), fun a => ?_⟩
  have := (MonoidHom.ofInjective hι).apply_symm_apply (φ.codRestrict ι.range h a)
  exact (congrArg Subtype.val this).symm

theorem inL_injective {O L : Type} [CommRing O] [IsLocalRing O] [Field L] [Algebra O L]
    (h : Function.Injective (algebraMap O L)) {n : ℕ} :
    Function.Injective (inL (O := O) (L := L) (n := n)) := by
  intro a b e
  apply Units.ext
  ext i j
  apply h
  have := congrArg (fun g : GL (Ix n) L => g.1 i j) e
  simpa using this

theorem mem_level_square_congruence_iff {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (ϖ : O) (κ : GL (Ix n) O) :
    κ ∈ Gam2 (n := n) ϖ ↔
      ∀ i j, κ.1 i j - (1 : Matrix (Ix n) (Ix n) O) i j ∈ Ideal.span {ϖ ^ 2} := by
  have h1 : (1 : Matrix (Ix n) (Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) =
      (1 : Matrix (Ix n) (Ix n) O).map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2})) :=
    (Matrix.map_one _ (map_zero _) (map_one _)).symm
  unfold Gam2
  rw [MonoidHom.mem_ker, Units.ext_iff, Units.val_one, h1]
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    exact Ideal.Quotient.eq.1 (by simpa using this)
  · intro h
    ext i j
    simpa using Ideal.Quotient.eq.2 (h i j)

theorem isOpen_ideal (D : D7) (v : Pl D) (ϖ : Ov D v) (h : ϖ ≠ 0) :
    IsOpen {x : Lv D v | ∃ y ∈ Ideal.span {ϖ ^ 2}, algebraMap (Ov D v) (Lv D v) y = x} := by
  have hc : algebraMap (Ov D v) (Lv D v) (ϖ ^ 2) ≠ 0 := by
    intro e
    exact pow_ne_zero 2 h (Subtype.val_injective (by simpa using e))
  set c := algebraMap (Ov D v) (Lv D v) (ϖ ^ 2) with hcdef
  have hO : IsOpen ((Valued.v.valuationSubring : ValuationSubring (Lv D v)) : Set (Lv D v)) :=
    Valued.isOpen_valuationSubring _
  have hs : {x : Lv D v | ∃ y ∈ Ideal.span {ϖ ^ 2}, algebraMap (Ov D v) (Lv D v) y = x} =
      (fun x => c⁻¹ * x) ⁻¹' ((Valued.v.valuationSubring : ValuationSubring (Lv D v)) : Set (Lv D v)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      have : c⁻¹ * algebraMap (Ov D v) (Lv D v) (z * ϖ ^ 2) = algebraMap (Ov D v) (Lv D v) z := by
        rw [map_mul, ← hcdef]; field_simp
      simp only [Set.mem_preimage, this]
      exact z.2
    · intro hx
      refine ⟨⟨c⁻¹ * x, hx⟩ * ϖ ^ 2, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), ?_⟩
      rw [map_mul, ← hcdef]
      have : algebraMap (Ov D v) (Lv D v) ⟨c⁻¹ * x, hx⟩ = c⁻¹ * x := rfl
      rw [this]; field_simp
  rw [hs]
  exact hO.preimage (continuous_const.mul continuous_id)

theorem continuous_entry (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (i j : Ix n) :
    Continuous fun k : KAt D n v => (thU D n v τ (proj D.sp.cm.sig (Jst D n) v k)).1 i j := by
  have h1 : Continuous fun k : KAt D n v =>
      splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v k) :=
    (continuous_splitHom τ).comp ((continuous_proj _ _ v).comp continuous_subtype_val)
  have h2 : Continuous fun k : KAt D n v =>
      (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v k)).1 :=
    Units.continuous_val.comp h1
  exact h2.matrix_elem (finSumFinEquiv i) (finSumFinEquiv j)

theorem exists_rho (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    ∃ ρ : KAt D n v →* GL (Ix n) (Ov D v),
      (∀ k : KAt D n v, thU D n v τ (proj D.sp.cm.sig (Jst D n) v k) = inL (L := Lv D v) (ρ k)) ∧
      Function.Surjective ρ ∧
      ∀ ϖ : Ov D v, Irreducible ϖ → MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) (Ov D v)))) := by
  have hinj : Function.Injective (inL (O := Ov D v) (L := Lv D v) (n := n)) :=
    inL_injective Subtype.val_injective
  have hmem : ∀ k : KAt D n v, ((thU D n v τ).comp ((proj D.sp.cm.sig (Jst D n) v).comp (KAt D n v).subtype)) k ∈
      (inL (O := Ov D v) (L := Lv D v) (n := n)).range := by
    intro k
    have hk : (k : G D n) ∈ GlobalTheory.LocIntw.KUpAd D.sp.cm.sig (Jst D n) := (Subgroup.mem_inf.1 k.2).1
    exact (GlobalTheory.T.mem_maximal_compact_iff_integral_image D n v τ _).1 ((GlobalTheory.LocIntw.mem_KUpAd.1 hk).1 v)
  obtain ⟨ρ, hρ⟩ := exists_lift _ _ hinj hmem
  have hρ' : ∀ k : KAt D n v, thU D n v τ (proj D.sp.cm.sig (Jst D n) v k) = inL (L := Lv D v) (ρ k) := hρ
  refine ⟨ρ, hρ', ?_, ?_⟩
  · intro κ
    obtain ⟨g, hg⟩ := (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).2 (inL (L := Lv D v) κ)
    have hK := (GlobalTheory.T.mem_maximal_compact_iff_integral_image D n v τ g).2 ⟨κ, hg.symm⟩
    have h1 : emb D.sp.cm.sig (Jst D n) v g ∈ KAt D n v :=
      Subgroup.mem_inf.2 ⟨GlobalTheory.LocIntw.emb_mem_KUpAd hK, by rw [← range_emb]; exact ⟨g, rfl⟩⟩
    refine ⟨⟨_, h1⟩, hinj ?_⟩
    rw [← hρ', proj_emb_self, hg]
  · intro ϖ hϖ
    have hU := isOpen_ideal D v ϖ hϖ.ne_zero
    set U := {x : Lv D v | ∃ y ∈ Ideal.span {ϖ ^ 2}, algebraMap (Ov D v) (Lv D v) y = x} with hUdef
    have hs : ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) (Ov D v))) =
        ⋂ i : Ix n, ⋂ j : Ix n, (fun k : KAt D n v =>
          (thU D n v τ (proj D.sp.cm.sig (Jst D n) v k)).1 i j - (1 : Matrix (Ix n) (Ix n) (Lv D v)) i j) ⁻¹' U := by
      ext k
      have he : ∀ i j, (thU D n v τ (proj D.sp.cm.sig (Jst D n) v k)).1 i j -
          (1 : Matrix (Ix n) (Ix n) (Lv D v)) i j =
          algebraMap (Ov D v) (Lv D v) ((ρ k).1 i j - (1 : Matrix (Ix n) (Ix n) (Ov D v)) i j) := by
        intro i j
        have h1 : (1 : Matrix (Ix n) (Ix n) (Lv D v)) i j =
            algebraMap (Ov D v) (Lv D v) ((1 : Matrix (Ix n) (Ix n) (Ov D v)) i j) := by
          by_cases h : i = j
          · subst h
            rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
          · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
        rw [hρ', map_sub, h1]
        rfl
      simp only [Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe, mem_level_square_congruence_iff, he, hUdef, Set.mem_setOf_eq]
      constructor
      · exact fun h i j => ⟨_, h i j, rfl⟩
      · intro h i j
        obtain ⟨y, hy, e⟩ := h i j
        have hA : Function.Injective (algebraMap (Ov D v) (Lv D v)) := Subtype.val_injective
        have e' := hA e
        rw [← e']
        exact hy
    rw [hs]
    refine IsOpen.measurableSet (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hU.preimage ?_)
    exact (continuous_entry D n v τ i j).sub continuous_const

end GlobalTheory.CompanionTheory.Jp.RhoSplit

end
end

section

open GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.section_eigenfunction_maximal_compact : GlobalTheory.CompanionTheory.Jp.SectionEigenfunctionMaximalCompact := by
  first | exact @GlobalTheory.CompanionTheory.Jp.B3.eigen_of_rightInvariant | exact GlobalTheory.CompanionTheory.Jp.B3.eigen_of_rightInvariant | (intros; apply GlobalTheory.CompanionTheory.Jp.B3.eigen_of_rightInvariant <;> assumption)
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem main : IdemEx → LatBound → QK → IkSch → ThetaSideMeasure := by
  intro _ hLat hQK hIk D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx
  have hdx := GlobalTheory.T.det_ne_zero_of_gram_nondegenerate D W b₀ hb x₀ hx
  have hDom := GlobalTheory.T.fundamental_domain_property
  have hOF := GlobalTheory.T.orbit_finiteness_of_lattice_bound hLat
  have hZ := GlobalTheory.T.zeta_polynomial_identity
  have hA := GlobalTheory.T.abscissa_convergence_identity
  have hJ := GlobalTheory.T.joined_projection_formula
  have hB := GlobalTheory.T.joined_block_formula
  have hE := GlobalTheory.T.extension_by_zero_orbit_formula
  have hS := GlobalTheory.T.unipotent_shift_invariance
  have hL := GlobalTheory.T.induced_section_local_integrability
  have hF := GlobalTheory.T.iterated_integrals_four_factors
  refine ⟨nuT hn I μ x₀, ⟨GlobalTheory.T.finite_on_compacts_orbit_measure D n t B W d hn I μ hμ b₀ hb x₀ hx, GlobalTheory.T.orbit_measure_concentrated_on_quadric hZ hA D n t B W d hn I μ hμ b₀ hb x₀ hx,
    fun h _ => GlobalTheory.T.orbit_measure_unitary_group_invariant hQK GlobalTheory.T.law_of_orbit_measure D n t B W d hn I μ hμ x₀ h,
    fun y _ => GlobalTheory.T.orbit_measure_translation_invariant D n t B W d hn I μ hμ x₀ y,
    fun g _ => GlobalTheory.T.orbit_measure_GL_right_scaling D n t B W d hn I μ hμ x₀ g⟩,
    GlobalTheory.T.orbit_measure_integral_points_nonzero D n t B W d hn I μ hμ x₀, fun Φ hΦ η hη => ?_⟩
  have hc := GlobalTheory.T.integrable_theta_kernel_product hIk hDom hOF hS hL hF hB D n t B W d hn I θ hθ μ hμ x₀ hdx Φ hΦ η hη
  obtain ⟨h1, h2⟩ := GlobalTheory.T.integrable_theta_kernel_fibers hZ hA hJ hE hF D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx Φ hΦ η hη hc
  exact ⟨h1, GlobalTheory.T.continuous_orbital_integral_unipotent hIk hDom hOF hS hB hE D n t B W d hn I θ hθ x₀ hdx Φ hΦ, h2⟩

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end
