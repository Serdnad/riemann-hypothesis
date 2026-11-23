module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle010
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Order.Real
public import ReciprocityTheory.Automorphisms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle024
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle023
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory

theorem multipliable_ofReal_re_of_complex (ι : Type) (c : ι → ℂ) (hc : Multipliable c)
    (hcr : ∀ i, (c i).im = 0 ∧ 0 ≤ (c i).re) :
    Multipliable (fun i => ENNReal.ofReal (c i).re) ∧
      ∏' i, ENNReal.ofReal (c i).re = ENNReal.ofReal (∏' i, c i).re := by
  obtain ⟨a, ha⟩ := hc
  have hc' : ∀ i, c i = ((c i).re : ℂ) := fun i => Complex.ext (by simp) (by simp [(hcr i).1])
  have hre : HasProd (fun i => (c i).re) a.re := by
    have h := (Complex.continuous_re.tendsto a).comp ha
    refine h.congr ?_
    intro s
    simp only [Function.comp]
    rw [Finset.prod_congr rfl (fun i _ => hc' i), ← Complex.ofReal_prod, Complex.ofReal_re]
  have h2 : HasProd (fun i => ENNReal.ofReal (c i).re) (ENNReal.ofReal a.re) := by
    have h := (ENNReal.continuous_ofReal.tendsto a.re).comp hre
    refine h.congr ?_
    intro s
    simp only [Function.comp]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (hcr i).2)]
  exact ⟨h2.multipliable, by rw [h2.tprod_eq, ha.tprod_eq]⟩

theorem multipliable_ofReal_re_of_complex' : ∀ (ι : Type) (c : ι → ℂ), Multipliable c → (∀ i, (c i).im = 0 ∧ 0 ≤ (c i).re) → Multipliable (fun i => ENNReal.ofReal (c i).re) ∧ ∏' i, ENNReal.ofReal (c i).re = ENNReal.ofReal (∏' i, c i).re :=
  multipliable_ofReal_re_of_complex

end GlobalTheory
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem det_fromBlocks_swapCols {R n : Type} [CommRing R] [Fintype n] [DecidableEq n]
    (A B C D : Matrix n n R) :
    (Matrix.fromBlocks A B C D).det = (-1) ^ Fintype.card n * (Matrix.fromBlocks B A D C).det := by
  have h : Matrix.fromBlocks A B C D =
      Matrix.fromBlocks B A D C * (Matrix.fromBlocks (1 : Matrix n n R) 1 0 1 *
        Matrix.fromBlocks (1 : Matrix n n R) 0 (-1) 1 * Matrix.fromBlocks (1 : Matrix n n R) 1 0 1 *
        Matrix.fromBlocks (-1 : Matrix n n R) 0 0 1) := by
    simp [Matrix.fromBlocks_multiply]
  rw [h]
  simp only [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, Matrix.det_neg, mul_one, one_mul]
  ring

theorem fromBlocks_updateRow_eq {R n : Type} [CommRing R] [Fintype n] [DecidableEq n]
    (Z Z' : Matrix n n R) (l : n) (a b c d : n → R) :
    ((Matrix.fromBlocks Z 0 0 Z').updateRow (Sum.inl l) (Sum.elim a b)).updateRow (Sum.inr l)
        (Sum.elim c d) =
      Matrix.fromBlocks (Z.updateRow l a) ((0 : Matrix n n R).updateRow l b)
        ((0 : Matrix n n R).updateRow l c) (Z'.updateRow l d) := by
  ext (i | i) (j | j) <;> by_cases h : i = l <;> simp [Matrix.updateRow_apply, h]

theorem det_updateRow_last_single {R : Type} [CommRing R] (r : ℕ)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (t : R) :
    (Z.updateRow (Fin.last r) (Pi.single (Fin.last r) t)).det =
      t * (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · have : (Z.updateRow (Fin.last r) (Pi.single (Fin.last r) t)).submatrix
        (Fin.last r).succAbove (Fin.last r).succAbove =
        Z.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp [Matrix.updateRow_apply, Fin.succAbove_last, Fin.castSucc_ne_last]
    rw [this]
    simp [← two_mul, pow_mul]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

theorem det_fromBlocks_rowBlocks {R n : Type} [CommRing R] [Fintype n] [DecidableEq n]
    (Z Z' : Matrix n n R) (l : n) (b c : n → R) :
    (Matrix.fromBlocks Z ((0 : Matrix n n R).updateRow l b)
        ((0 : Matrix n n R).updateRow l c) Z').det =
      Z.det * Z'.det - (Z.updateRow l c).det * (Z'.updateRow l b).det := by
  set F : (n ⊕ n → R) → (n ⊕ n → R) → R := fun u v =>
    (((Matrix.fromBlocks Z 0 0 Z').updateRow (Sum.inl l) u).updateRow (Sum.inr l) v).det with hF
  have hz : (0 : Matrix n n R).updateRow l 0 = 0 := by
    ext i j; simp [Matrix.updateRow_apply]
  have hz0 : ∀ X : Matrix n n R, (X.updateRow l 0).det = 0 := fun X =>
    Matrix.det_eq_zero_of_row_eq_zero l (by simp)
  have add2 : ∀ u v w, F u (v + w) = F u v + F u w := fun u v w => Matrix.det_updateRow_add _ _ _ _
  have add1 : ∀ u v w, F (u + v) w = F u w + F v w := fun u v w => by
    simp only [hF]
    have hne : (Sum.inl l : n ⊕ n) ≠ Sum.inr l := by simp
    rw [Matrix.updateRow_comm _ hne, Matrix.updateRow_comm _ hne, Matrix.updateRow_comm _ hne]
    exact Matrix.det_updateRow_add _ _ _ _
  have swap : ∀ u v, F u v = - F v u := fun u v => by
    simp only [hF]
    have hne : (Sum.inl l : n ⊕ n) ≠ Sum.inr l := by simp
    have : ((Matrix.fromBlocks Z 0 0 Z').updateRow (Sum.inl l) u).updateRow (Sum.inr l) v =
        (((Matrix.fromBlocks Z 0 0 Z').updateRow (Sum.inl l) v).updateRow (Sum.inr l) u).submatrix
          (Equiv.swap (Sum.inl l) (Sum.inr l)) id := by
      ext i j
      by_cases h1 : i = Sum.inl l
      · subst h1; simp [Matrix.updateRow_apply]
      · by_cases h2 : i = Sum.inr l
        · subst h2; simp [Matrix.updateRow_apply]
        · simp [Matrix.updateRow_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, h1, h2]
    rw [this, Matrix.det_permute, Equiv.Perm.sign_swap hne]
    simp
  have val : ∀ a b c d : n → R, F (Sum.elim a b) (Sum.elim c d) =
      (Matrix.fromBlocks (Z.updateRow l a) ((0 : Matrix n n R).updateRow l b)
        ((0 : Matrix n n R).updateRow l c) (Z'.updateRow l d)).det := fun a b c d => by
    simp only [hF, fromBlocks_updateRow_eq]
  have e : ∀ a b : n → R, Sum.elim a b = Sum.elim a (0 : n → R) + Sum.elim (0 : n → R) b := by
    intro a b; ext (i | i) <;> simp
  have h0 := val (Z l) b c (Z' l)
  rw [Matrix.updateRow_eq_self, Matrix.updateRow_eq_self] at h0
  rw [← h0, e (Z l) b, e c (Z' l), add1, add2, add2, swap (Sum.elim 0 b) (Sum.elim c 0)]
  simp only [val, hz, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂, hz0,
    Matrix.updateRow_eq_self]
  ring

theorem det_gram_two_frames {R : Type} [CommRing R] (r : ℕ)
    (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (T T' : R) :
    (Matrix.fromBlocks (Matrix.single (Fin.last r) (Fin.last r) (-T)) Z Z'
      (Matrix.single (Fin.last r) (Fin.last r) (-T'))).det =
      (-1) ^ (r + 1) * (Z.det * Z'.det - T * T' *
        ((Z.submatrix Fin.castSucc Fin.castSucc).det *
          (Z'.submatrix Fin.castSucc Fin.castSucc).det)) := by
  have hs : ∀ t : R, Matrix.single (Fin.last r) (Fin.last r) t =
      (0 : Matrix (Fin (r + 1)) (Fin (r + 1)) R).updateRow (Fin.last r)
        (Pi.single (Fin.last r) t) := by
    intro t
    ext i j
    simp only [Matrix.updateRow_apply, Matrix.single_apply, Pi.single_apply, Matrix.zero_apply]
    by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;>
      simp [hi, hj, eq_comm]
  rw [det_fromBlocks_swapCols, hs, hs, det_fromBlocks_rowBlocks, det_updateRow_last_single,
    det_updateRow_last_single, Fintype.card_fin]
  ring

end GlobalTheory.HL
end

section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.WeilOrbit

theorem measurableEmbedding_of_sigmaCompact {Y X : Type} [TopologicalSpace Y] [T2Space Y]
    [SigmaCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] {φ : Y → X} (hc : Continuous φ)
    (hi : Function.Injective φ) : MeasurableEmbedding φ := by
  refine ⟨hi, hc.measurable, fun s hs => ?_⟩
  have h : φ '' s = ⋃ n, (fun y : compactCovering Y n => φ y) '' (Subtype.val ⁻¹' s) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨n, hn⟩ := exists_mem_compactCovering y
      exact ⟨n, ⟨y, hn⟩, hy, rfl⟩
    · rintro ⟨n, y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [h]
  refine MeasurableSet.iUnion fun n => ?_
  haveI : CompactSpace (compactCovering Y n) :=
    isCompact_iff_compactSpace.mp (isCompact_compactCovering Y n)
  have hce : Topology.IsClosedEmbedding (fun y : compactCovering Y n => φ y) :=
    (hc.comp continuous_subtype_val).isClosedEmbedding (hi.comp Subtype.val_injective)
  exact hce.measurableEmbedding.measurableSet_image.mpr (measurable_subtype_coe hs)

theorem exists_compact_cover {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (H : Subgroup G) {C : Set (G ⧸ H)} (hC : IsCompact C) :
    ∃ K : Set G, IsCompact K ∧ C ⊆ (QuotientGroup.mk : G → G ⧸ H) '' K := by
  refine hC.induction_on (p := fun C => ∃ K : Set G, IsCompact K ∧
    C ⊆ (QuotientGroup.mk : G → G ⧸ H) '' K) ⟨∅, isCompact_empty, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨K, hK, h⟩
    exact ⟨K, hK, hst.trans h⟩
  · rintro s t ⟨K, hK, h⟩ ⟨L, hL, h'⟩
    exact ⟨K ∪ L, hK.union hL, by rw [Set.image_union]; exact Set.union_subset_union h h'⟩
  · intro q _
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨K, hK, hg⟩ := exists_compact_mem_nhds g
      exact ⟨_, mem_nhdsWithin_of_mem_nhds (QuotientGroup.isOpenMap_coe.image_mem_nhds hg),
        K, hK, subset_rfl⟩

def orbitMap (G : Type) {X : Type} [Group G] [MulAction G X] (x0 : X) :
    G ⧸ MulAction.stabilizer G x0 → X :=
  MulAction.ofQuotientStabilizer G x0

theorem orbitMap_mk {G X : Type} [Group G] [MulAction G X] (x0 : X) (g : G) :
    orbitMap G x0 (g : G ⧸ MulAction.stabilizer G x0) = g • x0 := rfl

theorem orbitMap_injective {G X : Type} [Group G] [MulAction G X] (x0 : X) :
    Function.Injective (orbitMap G x0) :=
  MulAction.injective_ofQuotientStabilizer G x0

theorem weil_formula : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MulAction G X] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (x0 : X), Continuous (fun p : G × X => p.1 • p.2) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (ν : Measure X), ν {y | ¬ ∃ g : G, g • x0 = y} = 0 → (∀ (g : G) (s : Set X), MeasurableSet s → ν ((fun y => g • y) ⁻¹' s) = ν s) → (∀ K : Set G, IsCompact K → ν ((fun g => g • x0) '' K) < ⊤) → ν ≠ 0 → ∃ μ' : Measure (MulAction.stabilizer G x0), μ'.IsHaarMeasure ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂μ' ∂ν := by
  intro G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ x0 hcont μ hμ ν hν0 hinv hfin hne
  set H := MulAction.stabilizer G x0 with hHdef
  have hc0 : Continuous (fun g : G => g • x0) :=
    hcont.comp (continuous_id.prodMk continuous_const)
  have hH : IsClosed (H : Set G) := isClosed_eq hc0 continuous_const
  haveI := hH
  letI : MeasurableSpace (G ⧸ H) := borel _
  haveI : BorelSpace (G ⧸ H) := ⟨rfl⟩
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace (G ⧸ H) := inferInstance
  let φ : G ⧸ H → X := orbitMap G x0
  have hφc : Continuous φ := (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr hc0
  have hφ : MeasurableEmbedding φ :=
    measurableEmbedding_of_sigmaCompact hφc (orbitMap_injective x0)
  have hrange : Set.range φ = {y | ∃ g : G, g • x0 = y} := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H g => exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨(g : G ⧸ H), rfl⟩
  have hae : ∀ᵐ y ∂ν, y ∈ Set.range φ := by
    rw [hrange]
    exact hν0
  have hmap : (ν.comap φ).map φ = ν := by
    rw [hφ.map_comap, Measure.restrict_eq_self_of_ae_mem hae]
  have hrad : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsInvariantRadon H (ν.comap φ) := by
    refine ⟨fun h0 => hne ?_, ⟨fun C hC => ?_⟩, ⟨fun g s hs => ?_⟩⟩
    · rw [← hmap, h0, Measure.map_zero]
    · obtain ⟨K, hK, hCK⟩ := exists_compact_cover H hC
      rw [hφ.comap_apply]
      refine (measure_mono ?_).trans_lt (hfin K hK)
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨g, hg, rfl⟩ := hCK hq
      exact ⟨g, hg, rfl⟩
    · rw [hφ.comap_apply, hφ.comap_apply, ← hinv g (φ '' s) (hφ.measurableSet_image.mpr hs)]
      congr 1
      have heq : ∀ (a : G) (q : G ⧸ H), φ (a • q) = a • φ q := by
        intro a q
        induction q using QuotientGroup.induction_on with
        | H b => exact mul_smul a b x0
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨g • q, hq, heq g q⟩
      · rintro ⟨q, hq, h⟩
        refine ⟨g⁻¹ • q, by simpa using hq, ?_⟩
        rw [heq, h, inv_smul_smul]
  let ν0 : Measure H := Measure.haar
  obtain ⟨dg, ⟨hdg, hq⟩, -⟩ :=
    GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon G H hH ν0 _ hrad
  let c := Measure.haarScalarFactor μ dg
  have hc : μ = c • dg := Measure.isMulLeftInvariant_eq_smul μ dg
  have hcpos : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ dg).ne'
  refine ⟨c • ν0, Measure.IsHaarMeasure.nnreal_smul ν0 hcpos, fun f hf s hs => ?_⟩
  have h1 : ∫⁻ y, ∫⁻ h' : H, f (s y * (h' : G)) ∂ν0 ∂ν = ∫⁻ g, f g ∂dg := by
    rw [(hq f hf).2]
    conv_lhs => rw [← hmap]
    rw [hφ.lintegral_map]
    refine lintegral_congr fun q => ?_
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk H ν0 f]
    congr 1
    apply orbitMap_injective x0
    rw [orbitMap_mk]
    exact hs _ (by
      have : φ q ∈ Set.range φ := ⟨q, rfl⟩
      rwa [hrange] at this)
  rw [hc]
  simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, h1]

end GlobalTheory.WeilOrbit
end

section

open MeasureTheory NumberField Finset

theorem _root_.GlobalTheory.T.regulator_le_sum_small_ideals_in_class : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → ∀ (C : ClassGroup (𝓞 K)) (S : Finset (Ideal (𝓞 K))), (∀ I, I ∈ S ↔ ∃ hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)), ClassGroup.mk0 ⟨I, hI⟩ = C ∧ (Ideal.absNorm I : ℝ) ≤ Real.sqrt |(discr K : ℝ)|) → Units.regulator K ≤ ∑ I ∈ S, Real.log (Real.sqrt |(discr K : ℝ)| / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ) := by
  first | exact @GlobalTheory.RegulatorClassBound.regulator_le_sum_class | exact GlobalTheory.RegulatorClassBound.regulator_le_sum_class | (intros; apply GlobalTheory.RegulatorClassBound.regulator_le_sum_class <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem tsum_pi_prod_ennreal : ∀ {ι : Type} [Fintype ι] {X : ι → Type} (φ : ∀ i, X i → ℝ≥0∞),
    ∑' x : ∀ i, X i, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  intro ι _
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ {X : ι → Type} (φ : ∀ i, X i → ℝ≥0∞),
      ∑' x : ∀ i, X i, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y) ?_ ?_ ?_ ι
  · intro α β _ e h X φ
    letI : Fintype α := Fintype.ofEquiv β e.symm
    have h1 := h (X := fun a => X (e a)) (fun a => φ (e a))
    rw [← (Equiv.piCongrLeft X e).tsum_eq]
    calc ∑' x : ∀ a, X (e a), ∏ b, φ b (Equiv.piCongrLeft X e x b)
        = ∑' x : ∀ a, X (e a), ∏ a, φ (e a) (x a) := by
          congr 1; ext x
          rw [← Fintype.prod_equiv e (fun a => φ (e a) (Equiv.piCongrLeft X e x (e a)))
            (fun b => φ b (Equiv.piCongrLeft X e x b)) (fun _ => rfl)]
          simp only [Equiv.piCongrLeft_apply_apply]
      _ = ∏ a, ∑' y, φ (e a) y := h1
      _ = ∏ b, ∑' y, φ b y := Fintype.prod_equiv e _ _ (fun _ => rfl)
  · intro X φ
    simp
  · intro α _ h X φ
    rw [← (Equiv.piOptionEquivProd (β := X)).symm.tsum_eq, Fintype.prod_option]
    rw [← h (X := fun a => X (some a)) (fun a => φ (some a))]
    rw [← ENNReal.tsum_mul_right]
    simp only [Fintype.prod_option]
    rw [ENNReal.tsum_prod']
    congr 1; ext y
    rw [← ENNReal.tsum_mul_left]
    rfl

end GlobalTheory.HL
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

theorem _root_.GlobalTheory.T.finiteAdelesCmField_eq_zero_of_components : ∀ (L : Type) [Field L] [NumberField L] (a : ReciprocityTheory.Aut.AL L), (∀ v, ReciprocityTheory.Aut.compAt L v a = 0) → a = 0 := by
  first | exact @GlobalTheory.AL_eq_zero_of_compAt | exact GlobalTheory.AL_eq_zero_of_compAt | (intros; apply GlobalTheory.AL_eq_zero_of_compAt <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

theorem _root_.GlobalTheory.T.splitPlaceProjection_eq_zero_of_placeComponent_eq_zero : ∀ (L : Type) [Field L] [NumberField L] (s : ReciprocityTheory.Aut.SplitPlace L) (a : ReciprocityTheory.Aut.AL L), ReciprocityTheory.Aut.compAt L s.v a = 0 → s.proj a = 0 := by
  first | exact @GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero | exact GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero | (intros; apply GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero <;> assumption)
end
