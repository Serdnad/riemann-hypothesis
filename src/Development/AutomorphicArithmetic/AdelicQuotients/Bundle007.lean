module

public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import GroundTheory.AutomorphicForms.Bundle016
public import GroundTheory.AutomorphicForms.QuotientMeasure
public import GroundTheory.AutomorphicForms.Bundle007
public import GroundTheory.AutomorphicForms.ReductionHeight
public import GroundTheory.AutomorphicForms.ReductionIwasawa
public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import GroundTheory.GlobalFields.SemilocalAlgebras.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private theorem entry_le {E : Type*} [NormedField E] {n : ℕ} (b m b' : GL (Fin n) E)
    (d : Fin n → Eˣ) (ρ : Fin n → ℝ) (hd : ∀ i, ‖((d i : Eˣ) : E)‖ = ρ i) (hρ : ∀ i, 0 < ρ i)
    (hb : ∀ p q : Fin n, q < p → (b : Matrix (Fin n) (Fin n) E) p q = 0)
    (hb' : ∀ p q : Fin n, q < p → (b' : Matrix (Fin n) (Fin n) E) p q = 0)
    (r : ℕ) (ε : ℝ) (hε : 0 < ε) (hr : ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → ρ j / ρ i ≤ ε)
    (i j : Fin n) (hi : (i : ℕ) < r) (hj : r ≤ (j : ℕ)) :
    ‖((b * diagUnits n d * m * (diagUnits n d)⁻¹ * b' : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E) j i‖ ≤
      (n : ℝ) ^ 2 * ε * (AutomorphicForm.locHeight b * AutomorphicForm.locHeight m *
        AutomorphicForm.locHeight b') := by
  have hinv : (((diagUnits n d)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      Matrix.diagonal fun i => (((d i)⁻¹ : Eˣ) : E) := by
    rw [← map_inv, coe_diagUnits]; rfl
  have e : ((b * diagUnits n d * m * (diagUnits n d)⁻¹ * b' : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E) j i =
      ∑ q, ∑ p, (b : Matrix (Fin n) (Fin n) E) j p * ((d p : Eˣ) : E) *
        (m : Matrix (Fin n) (Fin n) E) p q * (((d q)⁻¹ : Eˣ) : E) *
        (b' : Matrix (Fin n) (Fin n) E) q i := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hinv, coe_diagUnits,
      Matrix.mul_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by rw [Matrix.mul_diagonal]
  have hL : 0 ≤ AutomorphicForm.locHeight b * AutomorphicForm.locHeight m *
      AutomorphicForm.locHeight b' := by
    have h1 := AutomorphicForm.locHeight_pos b
    have h2 := AutomorphicForm.locHeight_pos m
    have h3 := AutomorphicForm.locHeight_pos b'
    positivity
  have term : ∀ p q : Fin n, ‖(b : Matrix (Fin n) (Fin n) E) j p * ((d p : Eˣ) : E) *
        (m : Matrix (Fin n) (Fin n) E) p q * (((d q)⁻¹ : Eˣ) : E) *
        (b' : Matrix (Fin n) (Fin n) E) q i‖ ≤
      ε * (AutomorphicForm.locHeight b * AutomorphicForm.locHeight m *
        AutomorphicForm.locHeight b') := by
    intro p q
    by_cases h1 : p < j
    · rw [hb j p h1]; simpa using mul_nonneg hε.le hL
    by_cases h2 : i < q
    · rw [hb' q i h2]; simpa using mul_nonneg hε.le hL
    have hp : r ≤ (p : ℕ) := hj.trans (Fin.not_lt.1 h1)
    have hq : (q : ℕ) < r := lt_of_le_of_lt (Fin.not_lt.1 h2) hi
    have hratio := hr q p hq hp
    have hq0 := hρ q
    have e2 : ‖(b : Matrix (Fin n) (Fin n) E) j p * ((d p : Eˣ) : E) *
        (m : Matrix (Fin n) (Fin n) E) p q * (((d q)⁻¹ : Eˣ) : E) *
        (b' : Matrix (Fin n) (Fin n) E) q i‖ =
        ρ p / ρ q * (‖(b : Matrix (Fin n) (Fin n) E) j p‖ * ‖(m : Matrix (Fin n) (Fin n) E) p q‖ *
          ‖(b' : Matrix (Fin n) (Fin n) E) q i‖) := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hd, hd]
      field_simp
    rw [e2]
    refine mul_le_mul hratio ?_ (by positivity) hε.le
    exact mul_le_mul (mul_le_mul (AutomorphicForm.norm_apply_le_locHeight b j p)
      (AutomorphicForm.norm_apply_le_locHeight m p q) (norm_nonneg _)
      (AutomorphicForm.locHeight_pos b).le) (AutomorphicForm.norm_apply_le_locHeight b' q i)
      (norm_nonneg _) (mul_nonneg (AutomorphicForm.locHeight_pos b).le
        (AutomorphicForm.locHeight_pos m).le)
  rw [e]
  calc _ ≤ ∑ _q : Fin n, ∑ _p : Fin n, ε * (AutomorphicForm.locHeight b *
        AutomorphicForm.locHeight m * AutomorphicForm.locHeight b') :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => term p q))
    _ = _ := by simp; ring

theorem UpperTheory.one_le_entry_bound_of_borel_diagonal_decomp :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (δ : GL (Fin n) K) (b b' m : AdelicGLn.AdelicGL K n),
          b ∈ (adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) → b' ∈ (adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) →
          ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i) (r : ℕ) (ε : ℝ), 0 < ε →
          (∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → ρ j / ρ i ≤ ε) →
          AdelicGLn.diagonal K n δ = b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * m *
            (diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)))⁻¹ * b' →
          ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → (δ : Matrix (Fin n) (Fin n) K) j i ≠ 0 →
          1 ≤ ((n : ℝ) ^ 2 * ε) ^ Module.finrank ℚ K * (AutomorphicForm.heightConst K n *
            (AutomorphicForm.height b * AutomorphicForm.height m * AutomorphicForm.height b')) ^ 2 := by
  intro K _ _ n δ b b' m hb hb' ρ hρ r ε hε hr hδ i j hi hj hc
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      finAt v (diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i))) = 1 := by
    intro v
    refine Units.ext (Matrix.ext fun p q => ?_)
    rw [finAt_apply, coe_diagUnits, Matrix.diagonal_apply, Units.val_one, Matrix.one_apply]
    split_ifs with h
    · subst h
      exact posIdele_finite (K := K) (ρ p) (hρ p) v
    · rfl
  have hv : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖(((δ : Matrix (Fin n) (Fin n) K) j i : K) : v.adicCompletion K)‖ ≤
        AutomorphicForm.locHeight (finAt v (b * m * b')) := by
    intro v
    have h1 : finAt v (AdelicGLn.diagonal K n δ) = finAt v (b * m * b') := by
      rw [hδ]
      simp only [finAt_mul, finAt_inv, hfin, mul_one, inv_one]
    have h2 := AutomorphicForm.norm_apply_le_locHeight (finAt v (b * m * b')) j i
    rw [← h1, finAt_apply, AdelicGLn.diagonal_apply] at h2
    rw [h1] at h2
    exact h2
  have hw : ∀ w : InfinitePlace K,
      ‖(((δ : Matrix (Fin n) (Fin n) K) j i : K) : w.Completion)‖ ≤
        (n : ℝ) ^ 2 * ε * (AutomorphicForm.locHeight (infAt w b) *
          AutomorphicForm.locHeight (infAt w m) * AutomorphicForm.locHeight (infAt w b')) := by
    intro w
    have h1 : infAt w (AdelicGLn.diagonal K n δ) =
        infAt w b * diagUnits n (fun i => posRealToUnits w ⟨ρ i ^ w.mult, pow_pos (hρ i) _⟩) *
          infAt w m * (diagUnits n (fun i => posRealToUnits w ⟨ρ i ^ w.mult, pow_pos (hρ i) _⟩))⁻¹ *
          infAt w b' := by
      rw [hδ]
      simp only [infAt_mul, infAt_inv, infAt_diagUnits_posIdele]
    have h2 := entry_le (infAt w b) (infAt w m) (infAt w b')
      (fun i => posRealToUnits w ⟨ρ i ^ w.mult, pow_pos (hρ i) _⟩) ρ
      (fun i => norm_posRealToUnits w (hρ i)) hρ
      (fun p q h => by rw [infAt_apply, mem_adelicBorel.1 hb h]; rfl)
      (fun p q h => by rw [infAt_apply, mem_adelicBorel.1 hb' h]; rfl)
      r ε hε hr i j hi hj
    rw [← h1, infAt_apply, AdelicGLn.diagonal_apply] at h2
    rw [AdeleRing.algebraMap_fst_apply] at h2
    exact h2
  have hN : 0 ≤ (n : ℝ) ^ 2 * ε := by positivity
  have pb := AutomorphicForm.height_pos b
  have pm := AutomorphicForm.height_pos m
  have pb' := AutomorphicForm.height_pos b'
  have hC := AutomorphicForm.one_le_heightConst (K := K) (n := n)
  have inf_le : ∀ g : AdelicGLn.AdelicGL K n,
      ∏ w : InfinitePlace K, AutomorphicForm.locHeight (infAt w g) ^ w.mult ≤
        AutomorphicForm.height g := fun g =>
    le_mul_of_one_le_right (zero_le_one.trans (AutomorphicForm.one_le_prod_locHeight g))
      (AutomorphicForm.one_le_finprod_locHeight g)
  have hI : ∏ w : InfinitePlace K, ‖(((δ : Matrix (Fin n) (Fin n) K) j i : K) : w.Completion)‖ ^ w.mult ≤
      ((n : ℝ) ^ 2 * ε) ^ Module.finrank ℚ K *
        (AutomorphicForm.height b * AutomorphicForm.height m * AutomorphicForm.height b') := by
    calc _ ≤ ∏ w : InfinitePlace K, ((n : ℝ) ^ 2 * ε * (AutomorphicForm.locHeight (infAt w b) *
          AutomorphicForm.locHeight (infAt w m) * AutomorphicForm.locHeight (infAt w b'))) ^ w.mult :=
          Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (norm_nonneg _) _)
            fun w _ => pow_le_pow_left₀ (norm_nonneg _) (hw w) _
      _ = ((n : ℝ) ^ 2 * ε) ^ Module.finrank ℚ K *
          ((∏ w : InfinitePlace K, AutomorphicForm.locHeight (infAt w b) ^ w.mult) *
           (∏ w : InfinitePlace K, AutomorphicForm.locHeight (infAt w m) ^ w.mult) *
           (∏ w : InfinitePlace K, AutomorphicForm.locHeight (infAt w b') ^ w.mult)) := by
          rw [← InfinitePlace.sum_mult_eq (K := K), ← Finset.prod_pow_eq_pow_sum]
          simp only [mul_pow, Finset.prod_mul_distrib]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hN _)
          have q1 := zero_le_one.trans (AutomorphicForm.one_le_prod_locHeight b)
          have q2 := zero_le_one.trans (AutomorphicForm.one_le_prod_locHeight m)
          have q3 := zero_le_one.trans (AutomorphicForm.one_le_prod_locHeight b')
          exact mul_le_mul (mul_le_mul (inf_le b) (inf_le m) q2 pb.le) (inf_le b') q3 (by positivity)
  have hF : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(((δ : Matrix (Fin n) (Fin n) K) j i : K) : v.adicCompletion K)‖ ≤
      AutomorphicForm.heightConst K n ^ 2 *
        (AutomorphicForm.height b * AutomorphicForm.height m * AutomorphicForm.height b') := by
    calc _ ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.locHeight (finAt v (b * m * b')) :=
          finprod_le_finprod₀ (Filter.eventually_cofinite.1 (eventually_norm_eq_one hc))
            (fun _ => norm_nonneg _) (AutomorphicForm.finite_mulSupport_locHeight_finAt _) hv
      _ ≤ AutomorphicForm.height (b * m * b') :=
          le_mul_of_one_le_left (zero_le_one.trans (AutomorphicForm.one_le_finprod_locHeight _))
            (AutomorphicForm.one_le_prod_locHeight _)
      _ ≤ AutomorphicForm.heightConst K n * AutomorphicForm.height (b * m) * AutomorphicForm.height b' :=
          AutomorphicForm.height_mul_le _ _
      _ ≤ AutomorphicForm.heightConst K n * (AutomorphicForm.heightConst K n *
            AutomorphicForm.height b * AutomorphicForm.height m) * AutomorphicForm.height b' := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (AutomorphicForm.height_mul_le _ _) (zero_le_one.trans hC)) pb'.le
      _ = _ := by ring
  have hC0 : 0 < AutomorphicForm.heightConst K n := zero_lt_one.trans_le hC
  calc (1 : ℝ) = _ := (prod_norm_mul_finprod_norm hc).symm
    _ ≤ (((n : ℝ) ^ 2 * ε) ^ Module.finrank ℚ K *
          (AutomorphicForm.height b * AutomorphicForm.height m * AutomorphicForm.height b')) *
        (AutomorphicForm.heightConst K n ^ 2 *
          (AutomorphicForm.height b * AutomorphicForm.height m * AutomorphicForm.height b')) :=
        mul_le_mul hI hF (finprod_nonneg fun _ => norm_nonneg _) (by positivity)
    _ = _ := by ring
end

section

open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.unimodular_finite_quotientMeasure_of_cocompact :
    ∀ (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (Λ : Subgroup T) [DiscreteTopology Λ] (ν : Measure T) [ν.IsHaarMeasure],
        (∃ C : Set T, IsCompact C ∧ ∀ t : T, ∃ g ∈ Λ, ∃ y ∈ C, t = g * y) →
        ν.IsMulRightInvariant ∧ ν.IsInvInvariant ∧ quotientMeasure Λ ν Set.univ < ⊤ := by
  intro T _ _ _ _ _ _ _ _ Λ _ ν _ hC
  obtain ⟨C, hC, h⟩ := hC
  haveI : CompactSpace (RightCosetSpace Λ) := by
    refine ⟨(hC.image (RightCosetSpace.continuous_mk Λ)).of_isClosed_subset isClosed_univ ?_⟩
    intro x _
    obtain ⟨t, rfl⟩ := RightCosetSpace.mk_surjective Λ x
    obtain ⟨g, hg, y, hy, rfl⟩ := h t
    exact ⟨y, hy, (RightCosetSpace.mk_mul_of_mem hg y).symm⟩
  haveI hr : ν.IsMulRightInvariant := RightCosetSpace.isMulRightInvariant_of_compactSpace Λ ν
  haveI := RightCosetSpace.isFiniteMeasure (Γ := Λ) ν
  exact ⟨hr, ⟨RightCosetSpace.inv_eq_self_of_isMulRightInvariant ν⟩, measure_lt_top _ _⟩
end

section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

theorem UpperTheory.charpoly_local_adelic_conj_diagonal_eq :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (γ : GL (Fin n) E) (x : AdelicGLn.AdelicGL E n),
        (∀ w : HeightOneSpectrum (𝓞 E), ((finAt w (x⁻¹ * AdelicGLn.diagonal E n γ * x) : GL (Fin n) (w.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly = (γ : Matrix (Fin n) (Fin n) E).charpoly.map (algebraMap E (w.adicCompletion E))) ∧
        ∀ w : InfinitePlace E, ((infAt w (x⁻¹ * AdelicGLn.diagonal E n γ * x) : GL (Fin n) w.Completion) :
          Matrix (Fin n) (Fin n) w.Completion).charpoly = (γ : Matrix (Fin n) (Fin n) E).charpoly.map (algebraMap E w.Completion) := by
  intro E _ _ n γ x
  refine ⟨fun w => ?_, fun w => ?_⟩
  · have h : ((finAt w (AdelicGLn.diagonal E n γ) : GL (Fin n) (w.adicCompletion E)) :
        Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
        (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) := by
      ext a b
      rfl
    rw [finAt_mul, finAt_mul, finAt_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj', h, Matrix.charpoly_map]
  · have h : ((infAt w (AdelicGLn.diagonal E n γ) : GL (Fin n) w.Completion) :
        Matrix (Fin n) (Fin n) w.Completion) =
        (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E w.Completion) := by
      ext a b
      rfl
    rw [infAt_mul, infAt_mul, infAt_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj', h, Matrix.charpoly_map]
end

section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

theorem UpperTheory.eq_one_of_smul_place_eq_of_completionMap_surjective :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (q : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E q), Function.Surjective (completionMap q w.1) →
        ∀ σ : E ≃ₐ[F] E, σ • w = w → σ = 1 := by
  intro F E _ _ _ _ _ q w hs σ hσ
  have h : w.1 = σ • w.1 := (congrArg Subtype.val hσ).symm
  haveI : w.1.asIdeal.LiesOver q.asIdeal := w.2
  have hid : ∀ y, galHom σ w.1 w.1 h y = y := by
    intro y
    obtain ⟨a, rfl⟩ := hs y
    exact galHom_completionMap q σ w.1 w.1 h a
  refine AlgEquiv.ext fun x ↦ ?_
  have h2 := galHom_algebraMap σ w.1 w.1 h x
  rw [hid] at h2
  exact (algebraMap E (w.1.adicCompletion E)).injective h2.symm
end

section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private theorem charpoly_scale {K : Type} [Field K] [Infinite K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) {c : K} (hc : c ≠ 0) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [Polynomial.scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly,
    Matrix.eval_charpoly, ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

private theorem coeff_zero_mem {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (hN : ∀ i j, N i j ∈ O) (q : K[X]) (hq : q.Monic)
    (hd : q ∣ N.charpoly) : q.coeff 0 ∈ O := by
  let N' : Matrix (Fin n) (Fin n) O := fun i j => ⟨N i j, hN i j⟩
  have hmap : N'.map (algebraMap O K) = N := by
    ext i j
    rfl
  have hd' : q ∣ (N'.charpoly).map (algebraMap O K) := by
    rw [← Matrix.charpoly_map, hmap]
    exact hd
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K (Matrix.charpoly_monic N') hd'
  rw [hq.leadingCoeff, map_one, mul_one] at hg
  rw [← hg, coeff_map]
  exact (g.coeff 0).2

theorem UpperTheory.norm_coeff_zero_dvd_charpoly_le_adicCompletion :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (R : ℝ), 1 ≤ R →
        (∀ i j, ‖M i j‖ ≤ R) → ∀ p : (w.adicCompletion E)[X], p.Monic → p ∣ M.charpoly → ‖p.coeff 0‖ ≤ R ^ n := by
  intro E _ _ w n M R hR hM p hp hd
  classical
  haveI : Infinite (w.adicCompletion E) :=
    Infinite.of_injective _ (algebraMap E (w.adicCompletion E)).injective

  let S : Finset (w.adicCompletion E) :=
    insert 1 (Finset.univ.image fun ij : Fin n × Fin n => M ij.1 ij.2)
  obtain ⟨c, hcS, hcmax⟩ := Finset.exists_max_image S (fun x => ‖x‖) ⟨1, Finset.mem_insert_self _ _⟩
  have hc1 : 1 ≤ ‖c‖ := by
    have := hcmax 1 (Finset.mem_insert_self _ _)
    simpa using this
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc1
    linarith
  have hcR : ‖c‖ ≤ R := by
    rcases Finset.mem_insert.1 hcS with rfl | h
    · simpa using hR
    · obtain ⟨ij, -, rfl⟩ := Finset.mem_image.1 h
      exact hM _ _
  have hent : ∀ i j, ‖M i j‖ ≤ ‖c‖ := fun i j =>
    hcmax _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))
  have hinv : c⁻¹ ≠ 0 := inv_ne_zero hc0
  have hint : ∀ x : w.adicCompletion E, ‖x‖ ≤ 1 → x ∈ w.adicCompletionIntegers E := fun x hx =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).2 (Valued.toNormedField.norm_le_one_iff.1 hx)
  have hint' : ∀ x : w.adicCompletion E, x ∈ w.adicCompletionIntegers E → ‖x‖ ≤ 1 := fun x hx =>
    Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 hx)
  have hN : ∀ i j, (c⁻¹ • M) i j ∈ w.adicCompletionIntegers E := by
    intro i j
    apply hint
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hent i j) (norm_nonneg _)
  have hq : (p.scaleRoots c⁻¹).Monic := (Polynomial.monic_scaleRoots_iff _).2 hp
  have hdq : p.scaleRoots c⁻¹ ∣ (c⁻¹ • M).charpoly := by
    rw [charpoly_scale M hinv]
    obtain ⟨r, hr⟩ := hd
    rw [hr, Polynomial.mul_scaleRoots_of_noZeroDivisors]
    exact dvd_mul_right _ _
  have hmem := hint' _ (coeff_zero_mem _ _ hN _ hq hdq)
  rw [Polynomial.coeff_scaleRoots, Nat.sub_zero, norm_mul, norm_pow, norm_inv, inv_pow] at hmem
  have hcpos : 0 < ‖c‖ ^ p.natDegree := by positivity
  have h1 : ‖p.coeff 0‖ ≤ ‖c‖ ^ p.natDegree := by
    rwa [← div_eq_mul_inv, div_le_one hcpos] at hmem
  have hdeg : p.natDegree ≤ n := by
    have := Polynomial.natDegree_le_of_dvd hd (Matrix.charpoly_monic M).ne_zero
    simpa [Matrix.charpoly_natDegree_eq_dim] using this
  calc ‖p.coeff 0‖ ≤ ‖c‖ ^ p.natDegree := h1
    _ ≤ R ^ p.natDegree := pow_le_pow_left₀ (norm_nonneg _) hcR _
    _ ≤ R ^ n := pow_le_pow_right₀ hR hdeg
end

section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private lemma norm_multiset_prod_le_pow (B : ℝ) (hB : 1 ≤ B) (s : Multiset ℂ)
    (hs : ∀ z ∈ s, ‖z‖ ≤ B) : ‖s.prod‖ ≤ B ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ']
    exact mul_le_mul (hs a (Multiset.mem_cons_self ..))
      (ih fun z hz => hs z (Multiset.mem_cons_of_mem hz)) (norm_nonneg _) (by linarith)

private lemma norm_root_charpoly_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : 1 ≤ R)
    (hM : ∀ i j, ‖M i j‖ ≤ R) (z : ℂ) (hz : M.charpoly.IsRoot z) :
    ‖z‖ ≤ max 1 (n : ℝ) * R := by
  have hdet : ((Matrix.scalar (Fin n)) z - M).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hz
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖) ⟨i0, Finset.mem_univ _⟩
  have hvi : 0 < ‖v i‖ := lt_of_lt_of_le (norm_pos_iff.mpr hi0) (hi i0 (Finset.mem_univ _))
  have hrow : z * v i = ∑ j, M i j * v j := by
    have h1 := congrFun hMv i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h1
    have h2 : ((Matrix.scalar (Fin n)) z).mulVec v i = z * v i := by
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rw [h2] at h1
    simpa [Matrix.mulVec, dotProduct] using h1
  have hle : ‖z‖ * ‖v i‖ ≤ n * R * ‖v i‖ := by
    rw [← norm_mul, hrow]
    calc ‖∑ j, M i j * v j‖ ≤ ∑ j, ‖M i j * v j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, R * ‖v i‖ := Finset.sum_le_sum (fun j _ => by
          rw [norm_mul]
          exact mul_le_mul (hM i j) (hi j (Finset.mem_univ _)) (norm_nonneg _) (by linarith))
      _ = n * R * ‖v i‖ := by simp [Finset.sum_const, mul_assoc]
  have h3 : ‖z‖ ≤ n * R := le_of_mul_le_mul_right hle hvi
  exact h3.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))

private lemma norm_coeff_zero_le_complex {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : 1 ≤ R)
    (hM : ∀ i j, ‖M i j‖ ≤ R) (p : ℂ[X]) (hp : p.Monic) (hd : p ∣ M.charpoly) :
    ‖p.coeff 0‖ ≤ (max 1 (n : ℝ) * R) ^ n := by
  have hB : 1 ≤ max 1 (n : ℝ) * R := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hR
  have hs : p.Splits := IsAlgClosed.splits p
  have hc : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  rw [hs.coeff_zero_eq_prod_roots_of_monic hp, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul]
  have hroots : ∀ z ∈ p.roots, ‖z‖ ≤ max 1 (n : ℝ) * R := fun z hz =>
    norm_root_charpoly_le M R hR hM z ((Polynomial.isRoot_of_mem_roots hz).dvd hd)
  refine (norm_multiset_prod_le_pow _ hB _ hroots).trans ?_
  rw [← hs.natDegree_eq_card_roots]
  refine pow_le_pow_right₀ hB ?_
  have h := natDegree_le_of_dvd hd hc
  simpa [Matrix.charpoly_natDegree_eq_dim] using h

theorem UpperTheory.norm_coeff_zero_dvd_charpoly_le_infinitePlace :
    ∀ (E : Type) [Field E] [NumberField E] (w : InfinitePlace E) (n : ℕ) (M : Matrix (Fin n) (Fin n) w.Completion) (R : ℝ), 1 ≤ R →
        (∀ i j, ‖M i j‖ ≤ R) → ∀ p : w.Completion[X], p.Monic → p ∣ M.charpoly → ‖p.coeff 0‖ ≤ (max 1 (n : ℝ) * R) ^ n := by
  intro E _ _ w n M R hR hM p hp hd
  have hn : ∀ x, ‖InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖ :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)
  have h := norm_coeff_zero_le_complex (M.map (InfinitePlace.Completion.extensionEmbedding w)) R hR
    (fun i j => by simpa [hn] using hM i j)
    (p.map (InfinitePlace.Completion.extensionEmbedding w))
    (hp.map _)
    (by rw [Matrix.charpoly_map]; exact Polynomial.map_dvd _ hd)
  rwa [coeff_map, hn] at h
end
